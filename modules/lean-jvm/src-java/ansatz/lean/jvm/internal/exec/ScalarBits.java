/*
 * Stateless scalar payload operations extracted from the JVM lambda-RC interpreter.
 * Upstream interpreter: Copyright (c) 2019 Microsoft Corporation. Apache-2.0.
 * Pinned Lean: 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
 */
package ansatz.lean.jvm.internal.exec;

/** Internal byte/bit operations only: no lane IDs, guest values, ownership or allocation policy. */
final class ScalarBits {
    private ScalarBits() { }

    /** Width is supplied by the engine's existing lane mapping (1, 2, 4 or 8). */
    static long readLittleEndian(byte[] payload,int offset,int width) {
        if(offset<0||offset>payload.length-width) throw new IllegalArgumentException("Scalar field outside payload");
        if(width==1) return Byte.toUnsignedInt(payload[offset]);
        long value=0;
        for(int i=0;i<width;i++) value|=(long)Byte.toUnsignedInt(payload[offset+i])<<(8*i);
        return value;
    }
    static void writeLittleEndian(byte[] payload,int offset,int width,long value) {
        if(offset<0||offset>payload.length-width) throw new IllegalArgumentException("Scalar field outside payload");
        if(width==1) { payload[offset]=(byte)value; return; }
        for(int i=0;i<width;i++) payload[offset+i]=(byte)(value>>>(8*i));
    }
    static boolean isNaN64Bits(long bits) {
        return (bits&0x7ff0000000000000L)==0x7ff0000000000000L&&(bits&0x000fffffffffffffL)!=0;
    }
    static boolean isNaN32Bits(int bits) {
        return (bits&0x7f800000)==0x7f800000&&(bits&0x007fffff)!=0;
    }
}
