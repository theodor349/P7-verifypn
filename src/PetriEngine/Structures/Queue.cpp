/* VerifyPN - TAPAAL Petri Net Engine
 * Copyright (C) 2016  Peter Gjøl Jensen <root@petergjoel.dk>
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

#include "PetriEngine/Structures/Queue.h"
#include "PetriEngine/PQL/Contexts.h"

#include <algorithm>
#include <cstddef>
#include <random>

namespace PetriEngine {
    namespace Structures {
        Queue::Queue(size_t) {}

        Queue::~Queue() {
        }


        BFSQueue::BFSQueue(size_t) : Queue() {}
        BFSQueue::~BFSQueue(){}

        size_t BFSQueue::pop()
        {
            if(!_queue.empty())
            {
                auto r = _queue.front();
                _queue.pop();
                return r;
            }
            else
            {
                return EMPTY;
            }
        }

        void BFSQueue::push(size_t id, PQL::DistanceContext*,
            const PQL::Condition* query)
        {
            _queue.push(id);
        }

        bool BFSQueue::empty() const {
            return _queue.empty();
        }

        DFSQueue::DFSQueue(size_t) : Queue() {}
        DFSQueue::~DFSQueue(){}

        size_t DFSQueue::pop()
        {
            if(_stack.empty()) return EMPTY;
            uint32_t n = _stack.top();
            _stack.pop();
            return n;
        }

        void DFSQueue::push(size_t id, PQL::DistanceContext*,
            const PQL::Condition* query)
        {
            _stack.push(id);
        }

        bool DFSQueue::empty() const {
            return _stack.empty();
        }

        /*bool DFSQueue::top() const {
            if(_stack.empty()) return EMPTY;
            uint32_t n = _stack.top();
            _states->decode(state, n);
            return true;
        }*/

        RDFSQueue::RDFSQueue(size_t seed) : Queue()
        {
            _rng.seed(seed);
        }

        RDFSQueue::~RDFSQueue(){}

        size_t RDFSQueue::pop()
        {
            if(_cache.empty())
            {
                if(_stack.empty())
                    return EMPTY;
                uint32_t n = _stack.top();
                _stack.pop();
                return n;
            }
            else
            {
                std::shuffle(_cache.begin(), _cache.end(), _rng);
                uint32_t n = _cache.back();
                for(size_t i = 0; i < (_cache.size() - 1); ++i)
                {
                    _stack.push(_cache[i]);
                }
                _cache.clear();
                return n;
            }
        }

        /*bool RDFSQueue::top(State &state) {
            if (!_cache.empty()) {
                std::shuffle ( _cache.begin(), _cache.end(), _rng );
                uint32_t n = _cache.back();
                _states->decode(state, n);
                for(size_t i = 0; i < _cache.size(); ++i)
                {
                    _stack.push(_cache[i]);
                }
                _cache.clear();
            }
            if (_stack.empty()) return EMPTY;
            uint32_t n = _stack.top();
            return n;
        }*/

        void RDFSQueue::push(size_t id, PQL::DistanceContext*,
            const PQL::Condition* query)
        {
            _cache.push_back(id);
        }

        bool RDFSQueue::empty() const {
            return _cache.empty() && _stack.empty();
        }

        HeuristicQueue::HeuristicQueue(size_t) : Queue() {}
        HeuristicQueue::~HeuristicQueue(){}

        size_t HeuristicQueue::pop()
        {
            if(_queue.empty()) return EMPTY;
            uint32_t n = _queue.top().item;
            _queue.pop();
            return n;
        }

        void HeuristicQueue::push(size_t id, PQL::DistanceContext* context,
            const PQL::Condition* query)
        {
            // invert result, highest numbers are on top!
            uint32_t dist = query->distance(*context);
            _queue.emplace(dist, (uint32_t)id);
        }

        bool HeuristicQueue::empty() const {
            return _queue.empty();
        }

        /*********************************************************************/
        /*                           POTENCY BOIIS                           */
        /*********************************************************************/

        PotencyQueue::PotencyQueue(size_t nTransitions, size_t s) : _queues(nTransitions)
        {
            if (nTransitions == 0)
                _queues = std::vector<std::priority_queue<weighted_t>>(1);

            _potencies.reserve(nTransitions);
            for (uint32_t i = 0; i < nTransitions; i++)
            {
                size_t prev = i == 0 ? SIZE_MAX : i - 1;
                size_t next = i == nTransitions - 1 ? SIZE_MAX : i + 1;
                _potencies.push_back(potency_t(100, prev, next));
            }
            _best = 0;
        }

        PotencyQueue::~PotencyQueue() {}

        std::tuple<size_t, uint32_t> PotencyQueue::pop()
        {
            if (_size == 0)
                return std::make_tuple(PetriEngine::PQL::EMPTY, PetriEngine::PQL::EMPTY);

            size_t t = _best;
            while (_queues[t].empty())
            {
                t = _potencies[t].next;
            }
            weighted_t n = _queues[t].top();
            _queues[t].pop();
            _size--;
            return std::make_tuple(n.item, n.weight);
        }

        void PotencyQueue::push(size_t id, PQL::DistanceContext *context, const PQL::Condition *query)
        {
            uint32_t dist = query->distance(*context);
            _queues[_best].emplace(dist, id);
            _size++;
        }

        bool PotencyQueue::empty() const
        {
            return _size == 0;
        }

        void PotencyQueue::_swapAdjacent(size_t a, size_t b)
        {
            // x <-> a <-> b <-> y
            // Assert: _potencies[a].next == b && _potencies[b].prev == a

            // x
            if (_potencies[a].prev != SIZE_MAX)
                _potencies[_potencies[a].prev].next = b;
            
            // y
            if (_potencies[b].next != SIZE_MAX)
                _potencies[_potencies[b].next].prev = a;
            
            // a
            size_t prevTmp = _potencies[a].prev;
            _potencies[a].prev = b;
            _potencies[a].next = _potencies[b].next;

            // b 
            _potencies[b].prev = prevTmp;
            _potencies[b].next = a;
        }

        IncrPotencyQueue::IncrPotencyQueue(size_t nTransitions, size_t) : PotencyQueue(nTransitions) {}
        IncrPotencyQueue::~IncrPotencyQueue() {}

        void IncrPotencyQueue::push(size_t id, PQL::DistanceContext *context, const PQL::Condition *query, uint32_t t,
                                uint32_t pDist)
        {
            uint32_t dist = query->distance(*context);

            if (dist < pDist)
            {
                _potencies[t].value += 1;
                while (_potencies[t].prev != SIZE_MAX && _potencies[t].value > _potencies[_potencies[t].prev].value)
                {
                    _swapAdjacent(_potencies[t].prev, t);
                }

                if (_potencies[t].prev == SIZE_MAX)
                    _best = t;
            }
            else if (dist > pDist && _potencies[t].value != 0)
            {
                _potencies[t].value -= 1;
                while (_potencies[t].next != SIZE_MAX && _potencies[t].value < _potencies[_potencies[t].next].value)
                {
                    if (_best == t)
                        _best = _potencies[t].next;

                    _swapAdjacent(t, _potencies[t].next);
                }
            }

            _queues[t].emplace(dist, id);
            _size++;
        }

        DistPotencyQueue::DistPotencyQueue(size_t nTransitions, size_t) : PotencyQueue(nTransitions) {}
        DistPotencyQueue::~DistPotencyQueue() {}

        void DistPotencyQueue::push(size_t id, PQL::DistanceContext *context, const PQL::Condition *query, uint32_t t,
                                uint32_t pDist)
        {
            uint32_t dist = query->distance(*context);

            if (dist < pDist)
            {
                _potencies[t].value += pDist - dist;
                while (_potencies[t].prev != SIZE_MAX && _potencies[t].value > _potencies[_potencies[t].prev].value)
                {
                    _swapAdjacent(_potencies[t].prev, t);
                }

                if (_potencies[t].prev == SIZE_MAX)
                    _best = t;
            }
            else if (dist > pDist && _potencies[t].value != 0)
            {
                if (_potencies[t].value >= dist - pDist)
                    _potencies[t].value -= dist - pDist;
                else
                    _potencies[t].value = 0;
                while (_potencies[t].next != SIZE_MAX && _potencies[t].value < _potencies[_potencies[t].next].value)
                {
                    if (_best == t)
                        _best = _potencies[t].next;

                    _swapAdjacent(t, _potencies[t].next);
                }
            }

            _queues[t].emplace(dist, id);
            _size++;
        }

        RandomPotencyQueue::RandomPotencyQueue(size_t nTransitions, size_t seed) : PotencyQueue(nTransitions), _seed(seed) {
            srand(_seed);
        }
        RandomPotencyQueue::~RandomPotencyQueue() {}

        void RandomPotencyQueue::push(size_t id, PQL::DistanceContext *context, const PQL::Condition *query, uint32_t t,
                                uint32_t pDist)
        {
            uint32_t dist = query->distance(*context);

            if (dist < pDist)
            {
                _potencies[t].value += pDist - dist;
                while (_potencies[t].prev != SIZE_MAX && _potencies[t].value > _potencies[_potencies[t].prev].value)
                {
                    _swapAdjacent(_potencies[t].prev, t);
                }

                if (_potencies[t].prev == SIZE_MAX)
                    _best = t;
            }
            else if (dist > pDist && _potencies[t].value != 0)
            {
                if (_potencies[t].value - 1 >= dist - pDist)
                    _potencies[t].value -= dist - pDist;
                else
                    _potencies[t].value = 1;
                while (_potencies[t].next != SIZE_MAX && _potencies[t].value < _potencies[_potencies[t].next].value)
                {
                    if (_best == t)
                        _best = _potencies[t].next;

                    _swapAdjacent(t, _potencies[t].next);
                }
            }

            _queues[t].emplace(dist, id);
            _size++;
        }

        std::tuple<size_t, uint32_t> RandomPotencyQueue::pop()
        {
            if (_size == 0)
                return std::make_tuple(PetriEngine::PQL::EMPTY, PetriEngine::PQL::EMPTY);
            
            if (_potencies.size() == 0)
            {
                weighted_t e = _queues[_best].top();
                _queues[_best].pop();
                _size--;
                return std::make_tuple(e.item, e.weight);
            }
            
            uint32_t n = 0;
            size_t current = SIZE_MAX;
            
            size_t t = _best;
            while (t != SIZE_MAX)
            {
                if (_queues[t].empty())
                {
                    t = _potencies[t].next;
                    continue;
                }

                n += _potencies[t].value;
                float r = (float) rand()/RAND_MAX;
                auto heehee = _potencies[t].value / (float)n;
                if (r <= heehee)
                    current = t;

                t = _potencies[t].next;
            }

            weighted_t e = _queues[current].top();
            _queues[current].pop();
            _size--;
            return std::make_tuple(e.item, e.weight);
        }


        /*********************************************************************/
        /*                           POTENCY BOIIS                           */
        /*********************************************************************/
    }
}
