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

/** Nat, Int, fixed-width word and float intrinsic families. Operands arrive as
 * mathematical carriers or raw scalar bits; results are published through the
 * interpreter's result/scalarResult registers. Owns no heap state. */
final class ScalarIntrinsics {
    private final Interpreter vm;

    ScalarIntrinsics(Interpreter vm) {
        this.vm=vm;
    }

    static boolean floatPrimitive(int op) { return op>=FLOAT_BITS&&op<=FLOAT_STRING||op==FLOAT_LE||op==FLOAT_ADD||op==FLOAT32_ADD
            ||op==FLOAT32_BITS||op==FLOAT32_DIV||op==FLOAT32_MUL||op==U64_FLOAT32
            ||op==FLOAT_TO_BITS||op==FLOAT32_TO_BITS; }
    strictfp void floatIntrinsic(Function f,long a,long b) {
        // Pinned object.cpp: both directions preserve non-NaN bits and canonicalize NaNs.
        if(f.intrinsic==FLOAT32_BITS||f.intrinsic==FLOAT32_TO_BITS) {
            int bits=(int)a;
            vm.scalarResult=ScalarBits.isNaN32Bits(bits)
                    ?0x7fc00000L:Integer.toUnsignedLong(bits); return;
        }
        if(f.intrinsic==U64_FLOAT32) {
            BigInteger unsigned=BigInteger.valueOf(a&Long.MAX_VALUE); if(a<0) unsigned=unsigned.setBit(63);
            // A direct integer-to-float conversion: routing through double would double-round.
            vm.scalarResult=Integer.toUnsignedLong(Float.floatToRawIntBits(unsigned.floatValue())); return;
        }
        if(f.intrinsic==FLOAT32_ADD||f.intrinsic==FLOAT32_DIV||f.intrinsic==FLOAT32_MUL) {
            float x=Float.intBitsToFloat((int)a),y=Float.intBitsToFloat((int)b);
            float out=f.intrinsic==FLOAT32_ADD?x+y:f.intrinsic==FLOAT32_DIV?x/y:x*y;
            vm.scalarResult=Integer.toUnsignedLong(Float.floatToRawIntBits(out)); return;
        }
        if(f.intrinsic==FLOAT_BITS||f.intrinsic==FLOAT_TO_BITS) { vm.scalarResult=ScalarBits.isNaN64Bits(a)?0x7ff8000000000000L:a; return; }
        if(f.intrinsic==FLOAT_U64) {
            BigInteger unsigned=BigInteger.valueOf(a&Long.MAX_VALUE); if(a<0) unsigned=unsigned.setBit(63);
            vm.scalarResult=Double.doubleToRawLongBits(unsigned.doubleValue()); return;
        }
        double x=Double.longBitsToDouble(a),y=Double.longBitsToDouble(b);
        switch(f.intrinsic) {
            case FLOAT_ADD: vm.scalarResult=Double.doubleToRawLongBits(x+y); break;
            case FLOAT_SUB: vm.scalarResult=Double.doubleToRawLongBits(x-y); break;
            case FLOAT_MUL: vm.scalarResult=Double.doubleToRawLongBits(x*y); break;
            case FLOAT_DIV: vm.scalarResult=Double.doubleToRawLongBits(x/y); break;
            case FLOAT_EQ: vm.scalarResult=x==y?1:0; break;
            case FLOAT_LT: vm.scalarResult=x<y?1:0; break;
            case FLOAT_LE: vm.scalarResult=x<=y?1:0; break;
            case FLOAT_STRING:
                if(ScalarBits.isNaN64Bits(a)) vm.result="NaN";
                else if(Double.isInfinite(x)) vm.result=x<0?"-inf":"inf";
                else {
                    BigDecimal rounded=new BigDecimal(x).setScale(6,RoundingMode.HALF_EVEN);
                    vm.result=(a<0&&rounded.signum()==0?"-":"")+rounded.toPlainString();
                }
                break;
            default: throw error("Unsupported Float intrinsic");
        }
    }
    static boolean borrowedIntPrimitive(int op) { return op>=INT_NEG&&op<=INT_NONNEG; }
    static BigInteger signedInteger(Object value) {
        if(value instanceof Long) return BigInteger.valueOf((Long)value);
        if(value instanceof BigInteger) return (BigInteger)value;
        throw error("Expected exact signed Int carrier");
    }
    private static Object normalizeSigned(BigInteger value) {
        return value.bitLength()<=63?Long.valueOf(value.longValue()):value;
    }
    void intIntrinsic(Function f,Object a,Object b,Object c) {
        // Int carriers are mathematical values. Native small-object thresholds and
        // raw tagged object words are deliberately not part of this profile.
        if(f.intrinsic==INT_NONNEG) { vm.scalarResult=signedInteger(a).signum()>=0?1:0; return; }
        if(f.intrinsic==INT_DIV_EXACT) require(ERASED.equals(c),"Int.divExact proof requires erased placeholder");
        if(a instanceof Long) {
            long x=(Long)a;
            if(f.intrinsic==INT_OF_NAT||f.intrinsic==INT_NEG_SUCC) {
                require(x>=0,"Invalid Nat"); vm.result=f.intrinsic==INT_OF_NAT?a:Long.valueOf(-x-1); return;
            }
            if(f.intrinsic==INT_NEG||f.intrinsic==INT_ABS) {
                if(x!=Long.MIN_VALUE) { vm.result=Long.valueOf(f.intrinsic==INT_NEG?-x:Math.abs(x)); return; }
            } else if(b instanceof Long) {
                long y=(Long)b;
                switch(f.intrinsic) {
                    case INT_EQ: vm.scalarResult=x==y?1:0; return;
                    case INT_LT: vm.scalarResult=x<y?1:0; return;
                    case INT_LE: vm.scalarResult=x<=y?1:0; return;
                    case INT_ADD:
                        try { vm.result=Long.valueOf(Math.addExact(x,y)); return; }
                        catch(ArithmeticException overflow) { break; }
                    case INT_SUB:
                        try { vm.result=Long.valueOf(Math.subtractExact(x,y)); return; }
                        catch(ArithmeticException overflow) { break; }
                    case INT_MUL:
                        try { vm.result=Long.valueOf(Math.multiplyExact(x,y)); return; }
                        catch(ArithmeticException overflow) { break; }
                    // Pinned lean.h/object.cpp: T-division truncates, T-modulus takes the
                    // dividend's sign; E-modulus is nonnegative. x/0=0 and x%0=x for all four.
                    case INT_DIV: case INT_DIV_EXACT:
                        if(y==0) { vm.result=Long.valueOf(0); return; }
                        if(x==Long.MIN_VALUE&&y==-1) break;
                        vm.result=Long.valueOf(x/y); return;
                    case INT_MOD: vm.result=y==0?a:Long.valueOf(x%y); return;
                    case INT_EDIV: {
                        if(y==0) { vm.result=Long.valueOf(0); return; }
                        if(x==Long.MIN_VALUE&&y==-1) break;
                        long q=x/y; if(x%y<0) q=y>0?q-1:q+1;
                        vm.result=Long.valueOf(q); return;
                    }
                    case INT_EMOD: {
                        if(y==0) { vm.result=a; return; }
                        long r=x%y;
                        // r-y cannot overflow: r<0 and |r|<|y| keep r+|y| within (0,2^63).
                        if(r<0) r=y>0?r+y:r-y;
                        vm.result=Long.valueOf(r); return;
                    }
                    default: throw error("Invalid signed Int intrinsic");
                }
            }
        }
        if(f.intrinsic==INT_OF_NAT) { vm.result=normalizeSigned(nat(a)); return; }
        if(f.intrinsic==INT_NEG_SUCC) { vm.result=normalizeSigned(boundedAdd(nat(a),BigInteger.ONE,false).negate()); return; }
        BigInteger x=signedInteger(a);
        if(f.intrinsic==INT_NEG) { boundedMagnitude(x); vm.result=normalizeSigned(x.negate()); return; }
        if(f.intrinsic==INT_ABS) { boundedMagnitude(x); vm.result=normalize(x.abs()); return; }
        BigInteger y=signedInteger(b);
        switch(f.intrinsic) {
            case INT_ADD: vm.result=normalizeSigned(boundedAdd(x,y,false)); return;
            case INT_SUB: vm.result=normalizeSigned(boundedAdd(x,y,true)); return;
            case INT_EQ: vm.scalarResult=x.equals(y)?1:0; return;
            case INT_LT: vm.scalarResult=x.compareTo(y)<0?1:0; return;
            case INT_LE: vm.scalarResult=x.compareTo(y)<=0?1:0; return;
            case INT_MUL: {
                BigInteger magnitude=vm.natMultiply(x.abs(),y.abs());
                vm.result=normalizeSigned(x.signum()*y.signum()<0?magnitude.negate():magnitude); return;
            }
            case INT_DIV: case INT_DIV_EXACT:
                vm.result=y.signum()==0?Long.valueOf(0):normalizeSigned(x.divide(y)); return;
            case INT_MOD: vm.result=normalizeSigned(y.signum()==0?x:x.remainder(y)); return;
            case INT_EDIV: {
                if(y.signum()==0) { vm.result=Long.valueOf(0); return; }
                BigInteger[] qr=x.divideAndRemainder(y); BigInteger q=qr[0];
                if(qr[1].signum()<0) q=y.signum()>0?q.subtract(BigInteger.ONE):q.add(BigInteger.ONE);
                vm.result=normalizeSigned(q); return;
            }
            case INT_EMOD: {
                if(y.signum()==0) { vm.result=normalizeSigned(x); return; }
                BigInteger r=x.remainder(y);
                vm.result=normalizeSigned(r.signum()<0?r.add(y.abs()):r); return;
            }
            default: throw error("Invalid signed Int intrinsic");
        }
    }
    /** Explicit membership: later IDs need not lie beside the original scalar group. */
    static boolean u64ScalarPrimitive(int op) {
        switch(op) {
            case U16_EQ: case U16_NAT: case U8_ADD: case U32_OWNED_NAT:
            case U8_FROM_NAT: case U16_FROM_NAT: case U8_OWNED_NAT: case U16_OWNED_NAT:
            case LAYOUT_FIELDS: case LAYOUT_SCALARS: case LAYOUT_TAG: case LAYOUT_USIZE: case U32_LT: case U64_TO_NAT:
            case STR_HASH: case U64_MIX: case U64_NAT: case U64_SHR: case U64_XOR: case U64_USIZE:
            case U64_LT: case U64_EQ: case U64_OWNED_NAT: case U64_TO_U32:
            case BOOL_U64: case U64_ADD: case U64_SUB: case U64_MUL: case U64_DIV: case U64_MOD:
            case U64_AND: case U64_OR: case U64_NOT: case U64_NEG: case U64_LOG2: case U64_SHL: case U64_LE:
            case U8_TO_U64: case U32_TO_U64: case USIZE_TO_U64: case U8_TO_U32: case U64_TO_U8:
                return true;
            default: return wordPrimitive(op);
        }
    }
    static void requireBoolScalar(Object value) {
        require(inputScalar(value,U8)<=1,"Bool.toUInt64 requires canonical Bool 0 or 1");
    }
    void scalarIntrinsic(Function f,Object a,Object b) {
        if(wordPrimitive(f.intrinsic)) { wordIntrinsic(f,a,b); return; }
        switch(f.intrinsic) {
            case USIZE_NAT:
                if(f.params.length>1) require(ERASED.equals(b),"USize conversion proof requires erased placeholder");
                vm.scalarResult=nat(a).longValue(); break;
            case USIZE_REPR: vm.result=Long.toUnsignedString((Long)a); break;
            case U16_NAT: case U32_NAT: vm.result=a; break;
            case U8_ADD: vm.scalarResult=((Long)a+(Long)b)&255L; break;
            case U16_EQ: case U32_EQ: vm.scalarResult=((Long)a).longValue()==((Long)b).longValue()?1:0; break;
            case U32_LT: vm.scalarResult=(Long)a<(Long)b?1:0; break;
            case U64_TO_NAT: vm.result=externalScalar((Long)a,U64); break;
            case LAYOUT_FIELDS: case LAYOUT_SCALARS: case LAYOUT_TAG: case LAYOUT_USIZE:
                requireLayoutUnit(a);
                vm.result=Long.valueOf(f.intrinsic==LAYOUT_FIELDS?256:f.intrinsic==LAYOUT_SCALARS?1024:f.intrinsic==LAYOUT_TAG?243:8); break;
            case U32_LE: vm.scalarResult=(Long)a<=(Long)b?1:0; break;
            case PLATFORM_BITS: require(a instanceof Long&&(Long)a==0,"Expected Unit for platform bits"); vm.result=Long.valueOf(64); break;
            case USIZE_LT: vm.scalarResult=Long.compareUnsigned((Long)a,(Long)b)<0?1:0; break;
            case USIZE_LE: vm.scalarResult=Long.compareUnsigned((Long)a,(Long)b)<=0?1:0; break;
            case USIZE_EQ: case U8_EQ: vm.scalarResult=((Long)a).longValue()==((Long)b).longValue()?1:0; break;
            case USIZE_ADD: vm.scalarResult=(Long)a+(Long)b; break;
            case USIZE_SUB: vm.scalarResult=(Long)a-(Long)b; break;
            case USIZE_MUL: vm.scalarResult=(Long)a*(Long)b; break;
            case USIZE_TO_NAT: vm.result=externalScalar((Long)a,USIZE); break;
            case USIZE_SHR: vm.scalarResult=(Long)a>>>(Long)b; break;
            case USIZE_SHL: vm.scalarResult=(Long)a<<(Long)b; break;
            case USIZE_AND: case U8_AND: vm.scalarResult=(Long)a&(Long)b; break;
            case U8_NAT: vm.result=a; break;
            case U8_LE: vm.scalarResult=(Long)a<=(Long)b?1:0; break;
            // Pinned lean.h: borrowed and consuming forms use modulo 2^width;
            // the optional ofNatLT proof is erased by the native C ABI.
            case U8_FROM_NAT: case U16_FROM_NAT:
                require(ERASED.equals(b),"Unsigned conversion proof requires erased placeholder");
                vm.scalarResult=nat(a).longValue()&(f.intrinsic==U8_FROM_NAT?255L:65535L); break;
            case U8_OWNED_NAT: case U16_OWNED_NAT:
                vm.scalarResult=nat(a).longValue()&(f.intrinsic==U8_OWNED_NAT?255L:65535L); vm.releaseQuiet(a,1); break;
            case U32_FROM_NAT:
                require(ERASED.equals(b),"UInt32 conversion proof requires erased placeholder");
                vm.scalarResult=nat(a).longValue()&0xffffffffL; break;
            case U32_TO_U8: vm.scalarResult=(Long)a&255; break;
            case U32_ADD: vm.scalarResult=((Long)a+(Long)b)&0xffffffffL; break;
            case STR_HASH: vm.scalarResult=stringHash(vm.utf8(a)); break;
            case U8_TO_U64: case U32_TO_U64: case USIZE_TO_U64: case U8_TO_U32: vm.scalarResult=(Long)a; break;
            case U64_TO_U8: vm.scalarResult=(Long)a&255L; break;
            case BOOL_U64: requireBoolScalar(a); vm.scalarResult=(Long)a; break;
            case U64_ADD: vm.scalarResult=(Long)a+(Long)b; break;
            case U64_SUB: vm.scalarResult=(Long)a-(Long)b; break;
            case U64_MUL: vm.scalarResult=(Long)a*(Long)b; break;
            case U64_DIV: vm.scalarResult=(Long)b==0?0:Long.divideUnsigned((Long)a,(Long)b); break;
            case U64_MOD: vm.scalarResult=(Long)b==0?(Long)a:Long.remainderUnsigned((Long)a,(Long)b); break;
            case U64_AND: vm.scalarResult=(Long)a&(Long)b; break;
            case U64_OR: vm.scalarResult=(Long)a|(Long)b; break;
            case U64_NOT: vm.scalarResult=~(Long)a; break;
            case U64_NEG: vm.scalarResult=-(Long)a; break;
            case U64_LOG2: vm.scalarResult=(Long)a==0?0:63-Long.numberOfLeadingZeros((Long)a); break;
            case U64_SHL: vm.scalarResult=(Long)a<<(Long)b; break;
            case U64_LE: vm.scalarResult=Long.compareUnsigned((Long)a,(Long)b)<=0?1:0; break;
            case U64_MIX: vm.scalarResult=mixHash((Long)a,(Long)b); break;
            case U64_NAT:
                if(f.params.length>1) require(ERASED.equals(b),"UInt64 conversion proof requires erased placeholder");
                vm.scalarResult=nat(a).longValue(); break;
            case U64_OWNED_NAT: vm.scalarResult=nat(a).longValue(); vm.releaseQuiet(a,1); break;
            case U32_OWNED_NAT: vm.scalarResult=nat(a).longValue()&0xffffffffL; vm.releaseQuiet(a,1); break;
            case U64_SHR: vm.scalarResult=(Long)a>>>(Long)b; break;
            case U64_XOR: vm.scalarResult=(Long)a^(Long)b; break;
            case U64_USIZE: vm.scalarResult=(Long)a; break;
            case U64_TO_U32: vm.scalarResult=(Long)a&0xffffffffL; break;
            case U64_LT: vm.scalarResult=Long.compareUnsigned((Long)a,(Long)b)<0?1:0; break;
            case U64_EQ: vm.scalarResult=((Long)a).longValue()==((Long)b).longValue()?1:0; break;
            default: throw error("Invalid scalar intrinsic");
        }
    }
    private static void boundedMagnitude(BigInteger value) {
        resource(magnitudeBits(value)<=MAX_NAT_RESULT_BITS,"Integer magnitude outside bounded runtime bit limit");
    }
    static Object natShiftLeft(BigInteger value,BigInteger exponent) {
        if(value.signum()==0) return ERASED;
        if(exponent.signum()==0) return normalize(value);
        resource(exponent.compareTo(BigInteger.valueOf(MAX_SHIFT_RESULT_BITS))<=0
                &&(long)value.bitLength()+exponent.longValue()<=MAX_SHIFT_RESULT_BITS,
                "Nat.shiftLeft result outside bounded runtime bit limit");
        return normalize(value.shiftLeft(exponent.intValue()));
    }
    static boolean natPrimitive(int op) {
        return op<=POW||(op>=NAT_LE&&op<=NAT_SHR)||(op>=NAT_AND&&op<=NAT_DIV_EXACT);
    }
    static boolean boolWordPrimitive(int op) {
        return op==BOOL_U64||(wordPrimitive(op)&&(op-WORD_BASE)%WORD_STRIDE==W_FROM_BOOL);
    }
    /** Pinned lean.h semantics: arithmetic wraps modulo 2^width, x/0=0, x%0=x,
     * shift distances reduce modulo the width, log2 0=0, and narrowing truncates. */
    private void wordIntrinsic(Function f,Object a,Object b) {
        int lane=(f.intrinsic-WORD_BASE)/WORD_STRIDE,code=(f.intrinsic-WORD_BASE)%WORD_STRIDE,bits=WORD_BITS[lane];
        long mask=bits==64?-1L:(1L<<bits)-1;
        if(code==W_OWNED_NAT) { vm.scalarResult=nat(a).longValue()&mask; vm.releaseQuiet(a,1); return; }
        if(code==W_FROM_BOOL) { requireBoolScalar(a); vm.scalarResult=(Long)a; return; }
        long x=(Long)a&mask,y=b instanceof Long?(Long)b&mask:0;
        switch(code) {
            case W_ADD: vm.scalarResult=(x+y)&mask; break;
            case W_SUB: vm.scalarResult=(x-y)&mask; break;
            case W_MUL: vm.scalarResult=(x*y)&mask; break;
            case W_DIV: vm.scalarResult=y==0?0:Long.divideUnsigned(x,y); break;
            case W_MOD: vm.scalarResult=y==0?x:Long.remainderUnsigned(x,y); break;
            case W_AND: vm.scalarResult=x&y; break;
            case W_OR: vm.scalarResult=x|y; break;
            case W_XOR: vm.scalarResult=x^y; break;
            case W_NOT: vm.scalarResult=~x&mask; break;
            case W_NEG: vm.scalarResult=-x&mask; break;
            case W_SHL: vm.scalarResult=(x<<(int)(y&(bits-1)))&mask; break;
            case W_SHR: vm.scalarResult=x>>>(int)(y&(bits-1)); break;
            case W_LOG2: vm.scalarResult=x==0?0:63-Long.numberOfLeadingZeros(x); break;
            case W_EQ: vm.scalarResult=x==y?1:0; break;
            case W_LT: vm.scalarResult=Long.compareUnsigned(x,y)<0?1:0; break;
            case W_LE: vm.scalarResult=Long.compareUnsigned(x,y)<=0?1:0; break;
            case W_TO_U8: case W_TO_U16: case W_TO_U32: case W_TO_U64: case W_TO_USIZE: {
                int target=WORD_BITS[code-W_TO_U8];
                vm.scalarResult=target==64?x:x&((1L<<target)-1); break;
            }
            default: throw error("Invalid word intrinsic");
        }
    }
}
