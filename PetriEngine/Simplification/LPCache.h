/* 
 * File:   LPFactory.h
 * Author: Peter G. Jensen
 *
 * Created on 31 May 2017, 09:26
 */

#ifndef LPFACTORY_H
#define LPFACTORY_H

#include <vector>
#include <unordered_set>
#include "MurmurHash2.h"
#include "Member.h"
#include "LinearProgram.h"
#include "Vector.h"


namespace PetriEngine {
    namespace Simplification {
        class LinearProgram;


        class LPCache {
        public:
            LPCache();
            virtual ~LPCache();
            Vector* createAndCache(const std::vector<int>& data)
            {
                auto res = vectors.insert(Vector(data));
                Vector& v = const_cast<Vector&>(*res.first);
                v.inc();
                assert(v.refs() > 0);
                return &v;
            }
            
            void invalidate(const Vector& vector)
            {
             //   vectors.erase(vector);
                assert(vector.refs() == 0);
            }

            LinearProgram* cacheProgram(LinearProgram&& program);
            void invalidate(LinearProgram* lp);
            
        private:
            // unordered_map does not invalidate on insert, only erase
            std::unordered_set<Vector> vectors;
            std::unordered_set<LinearProgram> programs;
        };

    }
}

#endif /* LPFACTORY_H */

