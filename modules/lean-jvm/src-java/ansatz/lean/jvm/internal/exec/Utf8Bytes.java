/*
 * Stateless UTF-8 byte operations extracted from the JVM lambda-RC interpreter.
 * Validator follows pinned Lean runtime/utf8.cpp.
 * Upstream UTF-8 validator: Copyright (c) 2014 Microsoft Corporation. Apache-2.0.
 * Author of upstream UTF-8 code: Leonardo de Moura.
 * Pinned Lean: 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
 */
package ansatz.lean.jvm.internal.exec;

/** Internal UTF-8 byte observations. Caller retains the existing extent and validation preconditions. */
final class Utf8Bytes {
    private Utf8Bytes() { }
    static boolean leadingByte(byte value) { return (value&0xc0)!=0x80; }
    static int width(byte value) {
        int b=Byte.toUnsignedInt(value);
        return b<128?1:b<224?2:b<240?3:4;
    }
    static int codePoint(byte[] bytes,int p) {
        int first=Byte.toUnsignedInt(bytes[p]),width=width(bytes[p]);
        int cp=width==1?first:first&((1<<(7-width))-1);
        for(int i=1;i<width;i++) cp=(cp<<6)|(bytes[p+i]&63);
        return cp;
    }
    /** Pinned runtime/utf8.cpp validator over the live prefix, with no ownership effects. */
    static boolean validPrefix(byte[] bytes,int size) {
        for(int at=0;at<size;) {
            int c=Byte.toUnsignedInt(bytes[at]);
            if(c<0x80) { at++; continue; }
            int length,min,code;
            if((c&0xe0)==0xc0) { length=2; min=0x80; code=c&0x1f; }
            else if((c&0xf0)==0xe0) { length=3; min=0x800; code=c&0x0f; }
            else if((c&0xf8)==0xf0) { length=4; min=0x10000; code=c&7; }
            else return false;
            if(length>size-at) return false;
            for(int i=1;i<length;i++) {
                int continuation=Byte.toUnsignedInt(bytes[at+i]);
                if((continuation&0xc0)!=0x80) return false;
                code=(code<<6)|(continuation&0x3f);
            }
            if(code<min||code>0x10ffff||(code>=0xd800&&code<=0xdfff)) return false;
            at+=length;
        }
        return true;
    }
}
