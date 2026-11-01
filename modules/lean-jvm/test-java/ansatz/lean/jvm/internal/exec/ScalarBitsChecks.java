package ansatz.lean.jvm.internal.exec;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;

/** Standalone value/byte contracts. Requires no engine, guest values, native code or framework. */
public final class ScalarBitsChecks {
    private static int checks;
    private static void check(boolean ok,String message) {
        checks++; if(!ok) throw new AssertionError(message);
    }
    private static void bounds(Runnable action) {
        try { action.run(); throw new AssertionError("Expected scalar payload bounds failure"); }
        catch(IllegalArgumentException error) {
            check(error.getClass()==IllegalArgumentException.class,"Scalar failure class changed");
            check("Scalar field outside payload".equals(error.getMessage()),"Scalar failure message changed");
        }
    }
    private static void scalarPayloads() {
        byte[] payload=new byte[24];
        long[] patterns={0,1,-1,Long.MIN_VALUE,Long.MAX_VALUE,0x0123456789abcdefL,0xfedcba9876543210L,
                0x80000000L,0x7fc01234L,0x7ff8000000001234L};
        for(int width:new int[]{1,2,4,8}) for(int offset:new int[]{0,1,payload.length-width}) for(long bits:patterns) {
            Arrays.fill(payload,(byte)0x5a);
            ScalarBits.writeLittleEndian(payload,offset,width,bits);
            long mask=width==8?-1L:(1L<<(width*8))-1;
            check(ScalarBits.readLittleEndian(payload,offset,width)==(bits&mask),"Scalar little-endian round trip");
            for(int i=0;i<width;i++) check(payload[offset+i]==(byte)(bits>>>(i*8)),"Scalar byte order");
            for(int i=0;i<payload.length;i++) if(i<offset||i>=offset+width)
                check(payload[i]==(byte)0x5a,"Scalar write changed bytes outside field");
        }
        for(int value=0;value<256;value++) {
            ScalarBits.writeLittleEndian(payload,3,1,value);
            check(ScalarBits.readLittleEndian(payload,3,1)==value,"Unsigned byte round trip");
        }
        for(int width:new int[]{1,2,4,8}) {
            bounds(()->ScalarBits.readLittleEndian(payload,-1,width));
            bounds(()->ScalarBits.writeLittleEndian(payload,-1,width,1));
            bounds(()->ScalarBits.readLittleEndian(payload,payload.length-width+1,width));
            bounds(()->ScalarBits.writeLittleEndian(payload,Integer.MAX_VALUE,width,1));
        }
        bounds(()->ScalarBits.readLittleEndian(new byte[7],0,8));
        bounds(()->ScalarBits.writeLittleEndian(new byte[7],0,8,1));
    }
    private static void nanPredicates() {
        for(long bits:new long[]{0,Long.MIN_VALUE,0x7ff0000000000000L,0xfff0000000000000L,
                0x0010000000000000L,1,0x7fefffffffffffffL})
            check(!ScalarBits.isNaN64Bits(bits),"Finite/infinite64 bits called NaN");
        for(long bits:new long[]{0x7ff0000000000001L,0x7ff8000000000000L,0xfff0000000000001L,0xfff8000000001234L})
            check(ScalarBits.isNaN64Bits(bits),"NaN64 bits not recognized");
        for(int bits:new int[]{0,Integer.MIN_VALUE,0x7f800000,0xff800000,0x00800000,1,0x7f7fffff})
            check(!ScalarBits.isNaN32Bits(bits),"Finite/infinite32 bits called NaN");
        for(int bits:new int[]{0x7f800001,0x7fc00000,0xff800001,0xffc01234})
            check(ScalarBits.isNaN32Bits(bits),"NaN32 bits not recognized");
    }
    private static byte[] bytes(int... values) {
        byte[] out=new byte[values.length]; for(int i=0;i<values.length;i++) out[i]=(byte)values[i]; return out;
    }
    private static void utf8Contracts() {
        for(int b=0;b<256;b++) {
            check(Utf8Bytes.leadingByte((byte)b)==(b<0x80||b>=0xc0),"UTF8 continuation classification");
            int width=b<128?1:b<224?2:b<240?3:4;
            check(Utf8Bytes.width((byte)b)==width,"UTF8 byte width classification");
        }
        int[] points={0,65,0x7f,0x80,0x7ff,0x800,0xd7ff,0xe000,0xffff,0x10000,0x1f600,0x10ffff};
        for(int point:points) {
            byte[] encoded=new String(Character.toChars(point)).getBytes(StandardCharsets.UTF_8);
            byte[] copy=encoded.clone();
            check(Utf8Bytes.validPrefix(encoded,encoded.length),"Valid scalar rejected");
            check(Utf8Bytes.codePoint(encoded,0)==point,"UTF8 code point decode");
            check(Utf8Bytes.width(encoded[0])==encoded.length,"UTF8 scalar width");
            check(Arrays.equals(copy,encoded),"UTF8 observation changed bytes");
            for(int prefix=1;prefix<encoded.length;prefix++)
                check(!Utf8Bytes.validPrefix(encoded,prefix),"Truncated scalar prefix accepted");
        }
        byte[][] malformed={bytes(0x80),bytes(0xbf),bytes(0xc0,0xaf),bytes(0xc1,0x80),bytes(0xc2),bytes(0xc2,0x41),
                bytes(0xe0,0x80,0xaf),bytes(0xe2,0x82),bytes(0xe2,0x28,0xa1),bytes(0xed,0xa0,0x80),bytes(0xed,0xbf,0xbf),
                bytes(0xf0,0x80,0x80,0xaf),bytes(0xf4,0x90,0x80,0x80),bytes(0xf5,0x80,0x80,0x80),
                bytes(0xf8,0x88,0x80,0x80,0x80),bytes(0xfe),bytes(0xff)};
        for(byte[] encoded:malformed) check(!Utf8Bytes.validPrefix(encoded,encoded.length),"Malformed UTF8 accepted");
        check(Utf8Bytes.validPrefix(new byte[0],0),"Empty UTF8 prefix");
        byte[] live=bytes(65,0x80);
        check(Utf8Bytes.validPrefix(live,1),"Validator inspected unused capacity");
        check(!Utf8Bytes.validPrefix(live,2),"Live malformed tail ignored");
        byte[] text="Aλ😀\u0000".getBytes(StandardCharsets.UTF_8);
        int at=0;
        for(int point:new int[]{65,0x3bb,0x1f600,0}) {
            check(Utf8Bytes.codePoint(text,at)==point,"Mixed UTF8 sequence offsets"); at+=Utf8Bytes.width(text[at]);
        }
        check(at==text.length&&Utf8Bytes.validPrefix(text,at),"Mixed UTF8 sequence extent");
    }
    public static void main(String[] args) {
        scalarPayloads(); nanPredicates(); utf8Contracts();
        System.out.println("ScalarBitsChecks PASS "+checks);
    }
}
