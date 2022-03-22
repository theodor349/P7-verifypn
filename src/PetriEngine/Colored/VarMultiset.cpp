/*
 * Authors:
 *      Nicolaj Østerby Jensen
 *      Jesper Adriaan van Diepen
 *      Mathias Mehl Sørensen
 */

#include "PetriEngine/Colored/VarMultiset.h"

namespace PetriEngine::Colored {
    VarMultiset::VarMultiset(const PetriEngine::Colored::Variable *v, const uint32_t multiplicity)
            : _set(), _type(v->colorType) {
        _set.emplace_back(v, multiplicity);
    }

    VarMultiset::Iterator VarMultiset::begin() const {
        return Iterator(this, 0);
    }

    VarMultiset::Iterator VarMultiset::end() const {
        return Iterator(this, _set.size());
    }

    VarMultiset VarMultiset::operator+(const VarMultiset &other) const {
        VarMultiset ms(*this);
        ms += other;
        return ms;
    }

    VarMultiset VarMultiset::operator-(const VarMultiset &other) const {
        VarMultiset ms(*this);
        ms -= other;
        return ms;
    }

    VarMultiset VarMultiset::operator*(uint32_t scalar) const {
        VarMultiset ms(*this);
        ms *= scalar;
        return ms;
    }

    void VarMultiset::operator+=(const VarMultiset &other) {
        if (_type == nullptr) _type = other._type;
        if (_type != other._type)
            throw base_error("You cannot compare variable multisets of different types");
        for (auto pair: other._set) {
            (*this)[pair.first] += pair.second;
        }
    }

    void VarMultiset::operator-=(const VarMultiset &other) {
        if (_type == nullptr) _type = other._type;
        if (other._type != nullptr && _type != other._type)
            throw base_error("You cannot add multisets over different sets");
        for (auto pair: _set) {
            (*this)[pair.first] = std::min<uint32_t>(pair.second - other[pair.first], 0); // min because underflow
        }
    }

    void VarMultiset::operator*=(uint32_t scalar) {
        for (auto &pair: _set) {
            pair.second *= scalar;
        }
    }

    uint32_t VarMultiset::operator[](const Variable *var) const {
        if (_type == nullptr || _type == var->colorType) {
            for (auto pair: _set) {
                if (pair.first == var) return pair.second;
            }
        }
        return 0;
    }

    uint32_t &VarMultiset::operator[](const Variable *var) {
        if (_type == nullptr) _type = var->colorType;
        if (_type != var->colorType) {
            throw base_error("You cannot access a multiset with a variable from a different color type");
        }
        for (auto &i: _set) {
            if (i.first == var) return i.second;
        }
        _set.emplace_back(var, 0);
        return _set.back().second;
    }

    size_t VarMultiset::size() const {
        size_t res = 0;
        for (auto pair: _set) {
            res += pair.second;
        }
        return res;
    }

    bool VarMultiset::isSubsetOf(const VarMultiset &other) const {
        VarMultiset thisMinusOther(*this);
        thisMinusOther -= other;
        VarMultiset otherMinusThis(other);
        otherMinusThis -= *this;
        return thisMinusOther.empty() && !otherMinusThis.empty();
    }

    std::string VarMultiset::toString() const {
        std::ostringstream oss;
        for (size_t i = 0; i < _set.size(); ++i) {
            oss << _set[i].second << "'" << _set[i].first->name;
            if (i < _set.size() - 1) {
                oss << " + ";
            }
        }
        return oss.str();
    }

    bool VarMultiset::Iterator::operator==(VarMultiset::Iterator &other) {
        return _ms == other._ms && _index == other._index;
    }

    bool VarMultiset::Iterator::operator!=(VarMultiset::Iterator &other) {
        return !(*this == other);
    }

    VarMultiset::Iterator &VarMultiset::Iterator::operator++() {
        ++_index;
        return *this;
    }

    std::pair<const Variable *, const uint32_t &> VarMultiset::Iterator::operator*() {
        return _ms->_set[_index];
    }
}