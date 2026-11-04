package ansatz.lean.jvm.internal.exec;

import java.io.ByteArrayOutputStream;
import java.math.BigInteger;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.lang.ref.WeakReference;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.concurrent.atomic.AtomicLong;
import java.security.SecureRandom;
import java.security.ProviderException;
import ansatz.lean.jvm.internal.fs.FileSession;
import ansatz.lean.jvm.internal.exec.ExternRegistry.*;
import ansatz.lean.jvm.internal.exec.Interpreter.*;
import static ansatz.lean.jvm.internal.exec.Interpreter.*;

/** Captured stdout/stderr accounting, standard-stream default retirement and the
 * managed sharing trace. Stream Nodes themselves are built by Interpreter. */
final class StdioCapture {
    private final Interpreter vm;

    StdioCapture(Interpreter vm) {
        this.vm=vm;
    }

    void retireCapturedDefaults() {
        // These synthetic roots have only private method closures/Long captures;
        // arbitrary guest finalizers are never dispatched by this quiet path.
        Node in=vm.stdinDefaultRoot,out=vm.stdoutRoot,err=vm.stderrRoot;
        vm.stdinDefaultRoot=null; vm.stdoutRoot=null; vm.stderrRoot=null;
        if(in!=null) vm.releaseQuiet(in,1); if(out!=null) vm.releaseQuiet(out,1); if(err!=null) vm.releaseQuiet(err,1);
    }
    Node directStream(int channel) { Node stream=vm.defaultStream(channel); vm.inc(stream,1); return stream; }
    /** Pinned object.cpp lean_mk_string_lossy_recover: replace a bad lead and
     * its following continuation run by ONE replacement character. Java's
     * decoder does not use this recovery rule for all malformed sequences. */
    String capturedText(byte[] bytes,int start,int end) {
        StringBuilder text=new StringBuilder(end-start);
        for(int at=start;at<end;) {
            if((at&1023)==0) vm.atomicPoll();
            int lead=Byte.toUnsignedInt(bytes[at]),width=0,min=0,cp=0;
            if(lead<128) { text.append((char)lead); at++; continue; }
            if((lead&0xe0)==0xc0) { width=2; min=0x80; cp=lead&31; }
            else if((lead&0xf0)==0xe0) { width=3; min=0x800; cp=lead&15; }
            else if((lead&0xf8)==0xf0) { width=4; min=0x10000; cp=lead&7; }
            boolean valid=width!=0&&width<=end-at;
            if(valid) for(int j=1;j<width;j++) {
                int next=Byte.toUnsignedInt(bytes[at+j]);
                if((next&0xc0)!=0x80) { valid=false; break; }
                cp=(cp<<6)|(next&63);
            }
            valid=valid&&cp>=min&&cp<=0x10ffff&&(cp<0xd800||cp>0xdfff);
            if(valid) { text.appendCodePoint(cp); at+=width; }
            else {
                text.append('\ufffd'); at++;
                while(at<end&&(bytes[at]&0xc0)==0x80) { if((at&1023)==0) vm.atomicPoll(); at++; }
            }
        }
        return text.toString();
    }
    void resetCapturedOutput() {
        if(vm.outputRaw.size()>65536) vm.outputRaw=new ByteArrayOutputStream(); else vm.outputRaw.reset();
        if(vm.stderrRaw.size()>65536) vm.stderrRaw=new ByteArrayOutputStream(); else vm.stderrRaw.reset();
        vm.output.setLength(0); vm.stderrOutput.setLength(0); vm.outputBytes=0; vm.stderrOutputBytes=0;
        if(vm.output.capacity()>65536) vm.output.trimToSize();
        if(vm.stderrOutput.capacity()>65536) vm.stderrOutput.trimToSize();
    }
    void captureBudget(int size,boolean stderr) {
        int previous=stderr?vm.stderrOutputBytes:vm.outputBytes,limit=stderr?vm.stderrLimit:vm.stdoutLimit;
        resource(size>=0&&size<=limit-previous,"Captured output outside bounded runtime profile");
    }
    void appendRaw(byte[] bytes,int start,int size,boolean stderr) {
        captureBudget(size,stderr); vm.atomicPoll();
        (stderr?vm.stderrRaw:vm.outputRaw).write(bytes,start,size);
        if(stderr) vm.stderrOutputBytes+=size; else vm.outputBytes+=size;
    }
    /** Pinned object.cpp: return the owning argument unchanged; the message is
     * borrowed and printed as a C string. Untracked immutable heap leaves have
     * no logical exclusivity observation in this runtime. Admitted programs
     * fail here if execution reaches a value outside that supported domain. */
    void validateTraceShared(Object erased,Object message,Object value) {
        require(ERASED.equals(erased),"Sharing trace requires erased type parameter");
        vm.utf8Extent(message);
        if(value instanceof Node) vm.node(value);
        else require(value instanceof Long&&(Long)value>=0,
                "Sharing trace requires a managed object or immediate scalar; heap-leaf ownership is unavailable");
    }
    void traceShared(Object erased,Object message,Object value) {
        validateTraceShared(erased,message,value);
        if(value instanceof Node&&!exclusive((Node)value)) {
            String text=(String)message;
            int end=text.indexOf('\0'); if(end<0) end=text.length();
            long bytes=11; // "shared RC " plus newline, before any output mutation.
            for(int i=0;i<end;i++) {
                char ch=text.charAt(i);
                if(Character.isHighSurrogate(ch)) { i++; bytes+=4; }
                else bytes+=ch<0x80?1:ch<0x800?2:3;
            }
            resource(bytes<=vm.stderrLimit-vm.stderrOutputBytes,
                    "Captured output outside bounded runtime profile");
            String line="shared RC "+text.substring(0,end)+"\n";
            vm.appendCaptured(line,true);
        }
        vm.result=value;
    }
    static final String[] STDIN_METHOD_LABELS={
        "IO.FS.Stream.ofBuffer._lam_4._boxed","IO.FS.Stream.ofBuffer._lam_0._boxed",
        "IO.FS.Stream.ofBuffer._lam_1._boxed","IO.FS.Stream.ofBuffer._lam_3._boxed",
        "IO.FS.Stream.ofBuffer._lam_2._boxed","IO.FS.instInhabitedStream.default._lam_5._boxed"};
    // These exact original body identities are checked against issued Headers;
    // accepted raw CAS/index authentication remains the trusted source adapter's job.
    static final String[] STDIN_METHOD_SHA={
        "e832604259e5794a331574c8a391637cde19e6f28ec322fc86a376a87b6c0c83","29e0f37498cc280d39c84ad0fa70336c5713b90308e32ee960d4ba28a7afbcac",
        "370ad89209e61c6fbe137e22e27d42200c02f50bb90cbaff442868ca0ecbd24a","41ab29cdd05e589e44148a3f6051b995992290d55733ab2bd234a1bed4c13ae6",
        "27399d0e9fd073070f6cc12f7d726b8c3d91cf17ec30e478eca80a81becfaa35","67b99a70a0d3bacecd41baf5e321468782636888e2b7a45febc15918216a7e89"};
    Node stdioDefault(int channel) { return channel==0?vm.stdinDefaultRoot:channel==1?vm.stdoutRoot:vm.stderrRoot; }
    void clearStdioDefault(int channel) {
        if(channel==0) vm.stdinDefaultRoot=null; else if(channel==1) vm.stdoutRoot=null; else vm.stderrRoot=null;
    }
    private boolean currentStdioRoots() {
        for(Node stream:vm.stdioContext.current) if(stream!=null) return true; return false;
    }
    boolean stdioRoots() {
        return vm.stdoutRoot!=null||vm.stdinDefaultRoot!=null||vm.stderrRoot!=null||(vm.stdioContext!=null&&currentStdioRoots());
    }
    void stepStdioDispose(RuntimeAction action) {
        if(action.stage==0) {
            if(action.cursor<3) {
                int channel=action.cursor++; Node old=vm.stdioContext.current[channel];
                action.retiring=old; action.releaseClaimed=false; vm.stdioContext.current[channel]=null;
                if(old!=null) { vm.beginRelease(old,1,ACTION_BODY); action.releaseClaimed=true; }
            } else if(action.cursor<vm.constants.length+3) {
                int index=action.cursor++-3;
                if(vm.constantReady[index]) {
                    Object old=vm.constants[index]; action.retiring=old; action.releaseClaimed=false;
                    vm.constants[index]=null; vm.constantReady[index]=false; vm.constantRetired[index]=true;
                    if(vm.program.functions[index].resultType==OBJ) { vm.beginRelease(old,1,ACTION_BODY); action.releaseClaimed=true; }
                }
            } else {
                if(currentStdioRoots()) { action.cursor=0; return; }
                for(boolean ready:vm.constantReady) if(ready) { action.cursor=0; return; }
                for(TaskRecord record:vm.taskRecords.values()) if(record.keepalive) { vm.phase=WAITING; return; }
                action.stage=1; action.cursor=0;
            }
        } else if(action.cursor<3) {
            // Validate all owned defaults immediately before the FIRST claim;
            // no guest advance or owner transfer separates this check/claim.
            // Also recheck each remaining graph at its own claim boundary.
            if(action.cursor==0) for(int i=0;i<3;i++) if(stdioDefault(i)!=null) vm.quietStdioGraph(stdioDefault(i));
            int channel=action.cursor; Node old=stdioDefault(channel);
            if(old!=null) vm.quietStdioGraph(old);
            action.cursor++;
            action.retiring=old; action.releaseClaimed=false; clearStdioDefault(channel);
            if(old!=null) { vm.beginRelease(old,1,ACTION_BODY); action.releaseClaimed=true; }
        } else { require(!stdioRoots(),"Stdio roots recreated during callback-free default retirement"); vm.disposed=true; vm.finishAction(action,ERASED); }
    }
}
