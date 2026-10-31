#include "ScalarObservation.h"
#include <cassert>

int main() {
    ScalarObservations observations;
    auto key=std::make_pair(size_t(8),size_t(0));
    ScalarObservation integer{true,4294967294ULL,-2};
    assert(observeScalar(observations,key,integer)==ScalarObservationStatus::fresh);
    assert(observeScalar(observations,key,integer)==ScalarObservationStatus::alias);
    assert(observeScalar(observations,key,{false,4294967294ULL,0})==ScalarObservationStatus::conflict);
    assert(observeScalar(observations,key,{true,4294967293ULL,-3})==ScalarObservationStatus::conflict);
    assert(observeScalar(observations,key,{true,4294967294ULL,4294967294LL})==ScalarObservationStatus::conflict);
    assert(observations.size()==1 && observations.at(key).agrees(integer));
    auto natural=std::make_pair(size_t(9),size_t(1));
    assert(observeScalar(observations,natural,{false,4294967294ULL,0})==ScalarObservationStatus::fresh);
    assert(observeScalar(observations,natural,{false,4294967294ULL,0})==ScalarObservationStatus::alias);
    assert(observeScalar(observations,natural,{true,4294967294ULL,-2})==ScalarObservationStatus::conflict);
    return 0;
}
