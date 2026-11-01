#pragma once
#include <cstdint>
#include <cstddef>
#include <map>
#include <utility>

struct ScalarObservation {
    bool isInt;
    size_t payload;
    int64_t signedValue;
    bool agrees(ScalarObservation const &other) const {
        return isInt==other.isInt && payload==other.payload &&
            (!isInt || signedValue==other.signedValue);
    }
};
enum class ScalarObservationStatus { fresh, alias, conflict };
using ScalarObservations=std::map<std::pair<size_t,size_t>,ScalarObservation>;

inline ScalarObservationStatus observeScalar(ScalarObservations &observations,
        std::pair<size_t,size_t> slot,ScalarObservation value) {
    auto [previous,fresh]=observations.emplace(slot,value);
    if(fresh) return ScalarObservationStatus::fresh;
    return previous->second.agrees(value)?ScalarObservationStatus::alias:ScalarObservationStatus::conflict;
}
