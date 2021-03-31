/* Copyright (C) 2021  Nikolaj J. Ulrik <nikolaj@njulrik.dk>,
 *                     Simon M. Virenfeldt <simon@simwir.dk>
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef VERIFYPN_BITPRODUCTSTATESET_H
#define VERIFYPN_BITPRODUCTSTATESET_H

#include "PetriEngine/Structures/StateSet.h"
#include "LTL/Structures/ProductState.h"
#include <cstdint>
#include <unordered_set>

namespace LTL::Structures {

    class ProductStateSetInterface {
    public:
        using stateid_t = size_t;
        using result_t = std::pair<bool, stateid_t>;

        virtual size_t getBuchiState(stateid_t id) = 0;

        virtual size_t getMarkingId(stateid_t id) = 0;

        virtual stateid_t getProductId(size_t markingId, size_t buchiState) = 0;

        virtual result_t add(const LTL::Structures::ProductState &state) = 0;

        virtual bool decode(LTL::Structures::ProductState &state, stateid_t id) = 0;

        virtual void setHistory(stateid_t id, size_t transition) {}

        virtual std::pair<size_t, size_t> getHistory(stateid_t stateid)
        {
            return std::make_pair(std::numeric_limits<size_t>::max(), std::numeric_limits<size_t>::max());
        }

        virtual size_t discovered() const = 0;

        virtual size_t max_tokens() const = 0;

        virtual ~ProductStateSetInterface() = default;

    };

    /**
     * Bit-hacking product state set for storing pairs (M, q) compactly in 64 bits.
     * Allows for a max of 2^nbits Büchi states and 2^(64-nbits) markings without overflow.
     * @tparam nbits the number of bits to allocate for Büchi state. Defaults to 16-bit. Max is 32-bit.
     */
    template<uint8_t nbits = 16>
    class BitProductStateSet : public ProductStateSetInterface {
    public:
        explicit BitProductStateSet(const PetriEngine::PetriNet &net, int kbound = 0)
                : markings(net, kbound, net.numberOfPlaces())
        {
        }

        static_assert(nbits <= 32, "Only up to 2^32 Büchi states supported");
        //using stateid_t = size_t;

        /**
         * bool success
         * size_t stateID; if error it is UINT64_MAX.
         */

        size_t getBuchiState(stateid_t id) override { return id >> buchiShift; }

        size_t getMarkingId(stateid_t id) override { return id & markingMask; }

        stateid_t getProductId(size_t markingId, size_t buchiState) override
        {
            return (buchiState << buchiShift) | (markingMask & markingId);
        }

/*#ifndef NDEBUG
            std::cerr << "markingMask: " << markingMask << '\n';
            std::cerr << "buchiMask:   " << buchiMask << std::endl;
#endif*/

        /**
         * Insert a product state into the state set.
         * @param state the product state to insert.
         * @return pair of [success, ID]
         */
        result_t add(const LTL::Structures::ProductState &state) override
        {
            ++_discovered;
            const auto[_, markingId] = markings.add(state);
            const stateid_t product_id = getProductId(markingId, state.getBuchiState());

            const auto[iter, is_new] = states.insert(product_id);
            assert(iter != std::end(states));
            return std::make_pair(is_new, product_id);
        }

        /**
         * Retrieve a product state from the state set.
         * @param id Composite state ID as previously generated by this.
         * @param state Output parameter to write product state to.
         * @return true if the state was successfully retrieved, false otherwise.
         */
        bool decode(LTL::Structures::ProductState &state, stateid_t id) override
        {
            const auto it = states.find(id);
            if (it == std::cend(states)) {
                return false;
            }
            auto marking_id = getMarkingId(*it);
            auto buchi_state = getBuchiState(*it);
            markings.decode(state, marking_id);
            state.setBuchiState(buchi_state);
            return true;
        }

        //size_t size() { return states.size(); }
        size_t discovered() const override { return _discovered; }

        size_t max_tokens() const override { return markings.maxTokens(); }

    protected:
        static constexpr auto markingMask = (1L << (64 - nbits)) - 1;
        static constexpr auto buchiMask = std::numeric_limits<size_t>::max() ^markingMask;
        static constexpr auto buchiShift = 64 - nbits;

        PetriEngine::Structures::StateSet markings;
        std::unordered_set<stateid_t> states;
        static constexpr auto err_val = std::make_pair(false, std::numeric_limits<size_t>::max());

        size_t _discovered = 0;
    };

    template<uint8_t nbytes = 16>
    class TraceableBitProductStateSet : public BitProductStateSet<nbytes> {
        using stateid_t = typename BitProductStateSet<nbytes>::stateid_t;
    public:
        explicit TraceableBitProductStateSet(const PetriEngine::PetriNet &net, int kbound = 0)
                : BitProductStateSet<nbytes>(net, kbound)
        {
        }

        bool decode(ProductState &state, stateid_t id) override
        {
            _parent = id;
            return BitProductStateSet<nbytes>::decode(state, id);
        }

        void setHistory(stateid_t id, size_t transition) override
        {
            _history[id] = {_parent, transition};
        }

        std::pair<size_t, size_t> getHistory(stateid_t stateid) override
        {
            auto[parent, trans] = _history.at(stateid);
            return std::make_pair(parent, trans);
        }

    private:
        struct history {
            size_t parent;
            size_t trans;
        };
        stateid_t _parent = 0;
        // product ID to parent ID
        std::unordered_map<size_t, history> _history;
    };
}

#endif //VERIFYPN_BITPRODUCTSTATESET_H
