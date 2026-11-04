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

/** String intrinsic family over immutable Java Strings and their UTF-8 bytes:
 * position arithmetic, comparison, memcmp, pushn, hashing and the bounded
 * String.any/isPrefixOf callback driver. Heap-inspecting views stay in Interpreter. */
final class StringIntrinsics {
    private final Interpreter vm;

    StringIntrinsics(Interpreter vm) {
        this.vm=vm;
    }

    /** Native strings use byte positions, including defined safe invalid-index
     * behavior. Java carriers are validated Unicode; no normalization occurs. */
    private void stringPositionIntrinsic(Function f,Object a,Object b,Object c) {
        byte[] bytes=vm.utf8(a); BigInteger position=nat(b);
        int length=bytes.length;
        if(f.intrinsic==STR_END) { vm.scalarResult=position.compareTo(BigInteger.valueOf(length))>=0?1:0; return; }
        if(f.intrinsic==STR_SAFE_NEXT) {
            int width=1;
            if(position.compareTo(BigInteger.valueOf(length))<0) {
                int p=position.intValue(); width=Utf8Bytes.leadingByte(bytes[p])?Utf8Bytes.width(bytes[p]):1;
            }
            vm.result=normalize(boundedAdd(position,BigInteger.valueOf(width),false)); return;
        }
        if(f.intrinsic==STR_PREV) {
            if(position.signum()==0) { vm.result=ERASED; return; }
            if(position.compareTo(BigInteger.valueOf(length))>0) { vm.result=normalize(position.subtract(BigInteger.ONE)); return; }
            int p=position.intValue()-1;
            while(p>0&&!Utf8Bytes.leadingByte(bytes[p])) p--;
            vm.result=Long.valueOf(p); return;
        }
        if(f.intrinsic==STR_VALID) {
            vm.scalarResult=position.compareTo(BigInteger.valueOf(length))<=0
                    &&(position.intValue()==length||Utf8Bytes.leadingByte(bytes[position.intValue()]))?1:0; return;
        }
        if(f.intrinsic==STR_EXTRACT) {
            BigInteger end=nat(c);
            if(position.bitLength()>63||end.bitLength()>63) { vm.result=a; return; }
            if(position.compareTo(end)>=0||position.compareTo(BigInteger.valueOf(length))>=0) { vm.result=""; return; }
            int begin=position.intValue();
            if(!Utf8Bytes.leadingByte(bytes[begin])) { vm.result=""; return; }
            int stop=end.compareTo(BigInteger.valueOf(length))>=0?length:end.intValue();
            if(stop<length&&!Utf8Bytes.leadingByte(bytes[stop])) stop=length;
            vm.result=new String(bytes,begin,stop-begin,StandardCharsets.UTF_8); return;
        }
        boolean inRange=position.compareTo(BigInteger.valueOf(length))<0;
        if(f.intrinsic==STR_BYTE) {
            require(ERASED.equals(c),"String byte proof requires erased placeholder");
            require(inRange,"UTF-8 byte index outside String");
            vm.scalarResult=Byte.toUnsignedInt(bytes[position.intValue()]); return;
        }
        if(f.intrinsic==STR_SET) {
            int replacement=vm.codePoint(c);
            if(!inRange||!Utf8Bytes.leadingByte(bytes[position.intValue()])) { vm.result=a; return; }
            int p=position.intValue(),width=Utf8Bytes.width(bytes[p]);
            stringReplacementExtent(length,width,replacement);
            vm.result=new String(bytes,0,p,StandardCharsets.UTF_8)+new String(Character.toChars(replacement))
                    +new String(bytes,p+width,length-p-width,StandardCharsets.UTF_8); return;
        }
        vm.scalarResult=inRange&&Utf8Bytes.leadingByte(bytes[position.intValue()])?Utf8Bytes.codePoint(bytes,position.intValue()):65;
    }
    void stringIntrinsic(Function f,Object a,Object b,Object c) {
        if(f.intrinsic>=STR_END&&f.intrinsic<=STR_EXTRACT||f.intrinsic==STR_BYTE||f.intrinsic==STR_SET) {
            stringPositionIntrinsic(f,a,b,c); return;
        }
        if(f.intrinsic==STR_LENGTH) { String s=vm.text(a); vm.utf8(s); vm.result=Long.valueOf(s.codePointCount(0,s.length())); return; }
        if(f.intrinsic==STR_CONTAINS) { String s=vm.text(a); vm.utf8(s); vm.scalarResult=s.indexOf(vm.codePoint(b))>=0?1:0; return; }
        byte[] x=vm.utf8(a),y=vm.utf8(b); int cmp=Arrays.compareUnsigned(x,y);
        if(f.intrinsic==STR_EQ) vm.scalarResult=cmp==0?1:0;
        else if(f.intrinsic==STR_LT) vm.scalarResult=cmp<0?1:0;
        else vm.scalarResult=cmp<0?0:cmp==0?1:2;
    }
    static boolean borrowedStringPositionPrimitive(int op) {
        return op==STR_GET||op==STR_NEXT||op==STR_EXTRACT;
    }
    void stringPosSet(Object source,Object position,Object replacement,Object proof) {
        require(ERASED.equals(proof),"String.Pos.set proof requires erased placeholder");
        byte[] bytes=vm.utf8(source); BigInteger offset=nat(position); int cp=vm.codePoint(replacement);
        require(offset.compareTo(BigInteger.valueOf(bytes.length))<0,"String.Pos.set requires a non-end position");
        int p=offset.intValue();
        require(Utf8Bytes.leadingByte(bytes[p]),"String.Pos.set requires a valid UTF-8 scalar position");
        int oldWidth=Utf8Bytes.width(bytes[p]); stringReplacementExtent(bytes.length,oldWidth,cp,"String.Pos.set");
        String changed=new String(bytes,0,p,StandardCharsets.UTF_8)+new String(Character.toChars(cp))
                +new String(bytes,p+oldWidth,bytes.length-p-oldWidth,StandardCharsets.UTF_8);
        vm.result=changed; vm.releaseQuiet(source,1); vm.releaseQuiet(position,1);
    }
    static boolean borrowedStringCompletionPrimitive(int op) { return op==STR_MEMCMP; }
    /** Proof-backed equality of raw UTF-8 byte ranges; neither positions nor
     * length may be narrowed until the complete range has been validated. */
    void stringMemcmp(Object left,Object right,Object leftStart,Object rightStart,Object size,Object leftProof,Object rightProof) {
        require(ERASED.equals(leftProof)&&ERASED.equals(rightProof),"String memcmp proofs require erased placeholders");
        byte[] a=vm.utf8(left),b=vm.utf8(right);
        BigInteger x=nat(leftStart),y=nat(rightStart),n=nat(size);
        require(x.compareTo(BigInteger.valueOf(a.length))<=0&&y.compareTo(BigInteger.valueOf(b.length))<=0
                &&n.compareTo(BigInteger.valueOf(a.length).subtract(x))<=0
                &&n.compareTo(BigInteger.valueOf(b.length).subtract(y))<=0,
                "String memcmp range outside bounded source domain");
        int from=x.intValue(),other=y.intValue(),count=n.intValue();
        vm.scalarResult=Arrays.equals(a,from,from+count,b,other,other+count)?1:0;
    }
    void stringCompletionIntrinsic(Function f,Object a,Object b,Object c) {
        if(f.intrinsic==STR_SUBSTRING_EQ) {
            // Validate BOTH owned operands before consuming either container.
            SubstringView x=vm.substringView(a),y=vm.substringView(b);
            long same=x.size==y.size&&Arrays.equals(x.bytes,x.start,x.start+x.size,y.bytes,y.start,y.start+y.size)?1:0;
            vm.releaseQuiet(x.owner,1); vm.releaseQuiet(y.owner,1); vm.scalarResult=same; return;
        }
        if(f.intrinsic==STR_POS_OF) {
            byte[] bytes=vm.utf8(a); int cp=vm.codePoint(b),p=0;
            while(p<bytes.length&&Utf8Bytes.codePoint(bytes,p)!=cp) p+=Utf8Bytes.width(bytes[p]);
            vm.result=Long.valueOf(p); vm.releaseQuiet(a,1); return;
        }
        if(f.intrinsic==STR_OFFSET_OF_POS) {
            byte[] bytes=vm.utf8(a); BigInteger position=nat(b);
            int stop=position.compareTo(BigInteger.valueOf(bytes.length))>=0?bytes.length:position.intValue();
            int p=0,count=0;
            while(p<stop) { p+=Utf8Bytes.width(bytes[p]); count++; }
            vm.result=Long.valueOf(count); vm.releaseQuiet(a,1); vm.releaseQuiet(b,1); return;
        }
        require(f.intrinsic==STR_PUSHN,"Invalid String completion intrinsic");
        String source=vm.text(a);
        require(source.length()<=MAX_STRING_OUTPUT_BYTES,"String.pushn output outside bounded runtime profile");
        int cp=vm.codePoint(b); BigInteger repetitions=nat(c); byte[] bytes=vm.utf8(source);
        int width=cp<0x80?1:cp<0x800?2:cp<0x10000?3:4;
        require(bytes.length<=MAX_STRING_OUTPUT_BYTES
                &&repetitions.compareTo(BigInteger.valueOf((MAX_STRING_OUTPUT_BYTES-bytes.length)/width))<=0,
                "String.pushn output outside bounded runtime profile");
        int count=repetitions.intValue();
        if(count==0) { vm.result=source; vm.releaseQuiet(c,1); return; }
        int chars=Math.addExact(source.length(),Math.multiplyExact(Character.charCount(cp),count));
        StringBuilder output=new StringBuilder(chars); output.append(source);
        for(int i=0;i<count;i++) output.appendCodePoint(cp);
        vm.result=output.toString(); vm.releaseQuiet(a,1); vm.releaseQuiet(c,1);
    }
    private long stringPredicateResult(Object answer) {
        require(answer instanceof Long&&((Long)answer==0||(Long)answer==1),
                "String.any predicate did not return canonical boxed Bool");
        return (Long)answer;
    }
    boolean stringIsPrefix(Object prefix,Object value) {
        vm.atomicPoll(); vm.utf8Extent(prefix); vm.utf8Extent(value); vm.atomicPoll();
        String p=vm.text(prefix),s=vm.text(value);
        if(p.length()>s.length()) return false;
        for(int i=0;i<p.length();i++) {
            if((i&1023)==0) vm.atomicPoll();
            if(p.charAt(i)!=s.charAt(i)) return false;
        }
        return true;
    }
    void stringAnyRecursive(Object[] args) {
        vm.validateStringAny(args); String text=vm.text(args[0]); Node predicate=(Node)args[1];
        long answer=0;
        for(int cursor=0;cursor<text.length();) {
            vm.atomicPoll(); vm.tick(); int cp=text.codePointAt(cursor); cursor+=Character.charCount(cp);
            vm.inc(predicate,1);
            answer=stringPredicateResult(vm.apply(predicate,new Object[]{Long.valueOf(cp)}));
            if(answer!=0) break;
        }
        vm.releaseQuiet(predicate,1); vm.scalarResult=answer;
    }
    void stepStringAny(RuntimeAction action) {
        String text=vm.text(action.arguments[0]);
        if(action.stage==1) {
            action.pending=(int)stringPredicateResult(vm.objects[action.slot]);
            vm.objects[action.slot]=null; action.work=null; action.stage=0;
        }
        if(action.stage==0) {
            vm.atomicPoll();
            if(action.pending==0&&action.cursor<text.length()) {
                vm.tick(); int cp=text.codePointAt(action.cursor); action.cursor+=Character.charCount(cp);
                action.work=new Object[]{Long.valueOf(cp)};
                vm.inc(action.arguments[1],1); action.stage=1;
                // Generic AP owns this retained callback occurrence and packet.
                vm.applyExplicit(action.arguments[1],action.work,ACTION_BODY,action.slot); return;
            }
            action.stage=2; action.retiring=action.arguments[1]; action.releaseClaimed=false;
        }
        if(action.stage==2) {
            action.stage=3;
            // Release can suspend in a captured finalizer; never replay DEC.
            if(vm.beginRelease(action.retiring,1,ACTION_BODY)) return;
        }
        require(action.stage==3,"Invalid String.any continuation");
        action.arguments=null; action.work=null; action.retiring=null;
        vm.finishAction(action,Long.valueOf(action.pending));
    }
    static long stringHash(byte[] bytes) {
        long m=0xc6a4a7935bd1e995L,hash=11L^((long)bytes.length*m);
        int end=bytes.length&~7;
        for(int offset=0;offset<end;offset+=8) {
            long key=0;
            for(int i=0;i<8;i++) key|=(long)Byte.toUnsignedInt(bytes[offset+i])<<(i*8);
            key*=m; key^=key>>>47; key*=m; hash^=key; hash*=m;
        }
        if(end<bytes.length) {
            for(int i=end;i<bytes.length;i++) hash^=(long)Byte.toUnsignedInt(bytes[i])<<((i-end)*8);
            hash*=m;
        }
        hash^=hash>>>47; hash*=m; hash^=hash>>>47; return hash;
    }
}
