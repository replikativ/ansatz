#include <cfenv>
#include <clocale>
#include <cstdint>
#include <cstring>
extern "C" double lean_float_of_bits(uint64_t);
static uint64_t rawWord(double value) {
    uint64_t word; std::memcpy(&word,&value,sizeof(word)); return word;
}
extern "C" uint8_t ansatz_f64_canonical_nan(void*) {
    return rawWord(lean_float_of_bits(0x7ff0000000000001ULL))==0x7ff8000000000000ULL
        && rawWord(lean_float_of_bits(0xfff8000000000042ULL))==0x7ff8000000000000ULL;
}
extern "C" uint8_t ansatz_f64_nearest(void*) { return std::fegetround()==FE_TONEAREST; }
extern "C" uint8_t ansatz_f64_c_locale(void*) {
    const char* locale=std::setlocale(LC_NUMERIC,nullptr);
    return locale&&std::strcmp(locale,"C")==0;
}
// Lean --run's native-opaque lookup consumes the boxed Lean ABI. UInt8 is
// an immediate lean_box(value); Unit is borrowed/ignored, with no heap values.
extern "C" void* l_nearest___boxed(void* unit) {
    return reinterpret_cast<void*>((uintptr_t(ansatz_f64_nearest(unit))<<1)|1);
}
extern "C" void* l_cLocale___boxed(void* unit) {
    return reinterpret_cast<void*>((uintptr_t(ansatz_f64_c_locale(unit))<<1)|1);
}
extern "C" void* l_canonicalNaN___boxed(void* unit) {
    return reinterpret_cast<void*>((uintptr_t(ansatz_f64_canonical_nan(unit))<<1)|1);
}
