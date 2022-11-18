/*
 *  Copyright Peter G. Jensen, all rights reserved.
 */

#include "PetriEngine/PQL/Contexts.h"

#include <iostream>

namespace PetriEngine
{
    namespace PQL
    {

        bool ColoredAnalysisContext::resolvePlace(const shared_const_string &place, std::function<void(const shared_const_string &)> &&fn)
        {
            auto it = _coloredPlaceNames.find(place);
            if (it != _coloredPlaceNames.end())
            {
                for (auto &[_, name] : it->second)
                    fn(name);
                return true;
            }
            return false;
        }

        bool ColoredAnalysisContext::resolveTransition(const shared_const_string &transition, std::function<void(const shared_const_string)> &&fn)
        {
            auto it = _coloredTransitionNames.find(transition);
            if (it != _coloredTransitionNames.end())
            {
                for (auto &e : it->second)
                    fn(e);
                return true;
            }
            return false;
        }

        AnalysisContext::ResolutionResult AnalysisContext::resolve(const shared_const_string &identifier, bool place)
        {
            ResolutionResult result;
            result.offset = -1;
            result.success = false;
            auto &map = place ? _placeNames : _transitionNames;
            auto it = map.find(identifier);
            if (it != map.end())
            {
                result.offset = (int)it->second;
                result.success = true;
                return result;
            }
            return result;
        }

        uint32_t SimplificationContext::getLpTimeout() const
        {
            return _lpTimeout;
        }

        double SimplificationContext::getReductionTime()
        {
            // duration in seconds
            auto end = std::chrono::high_resolution_clock::now();
            return (std::chrono::duration_cast<std::chrono::microseconds>(end - _start).count()) * 0.000001;
        }

        glp_prob *SimplificationContext::makeBaseLP() const
        {
            if (_base_lp == nullptr)
                _base_lp = buildBase();
            if (_base_lp == nullptr)
                return nullptr;
            auto *tmp_lp = glp_create_prob();
            glp_copy_prob(tmp_lp, _base_lp, GLP_OFF);
            return tmp_lp;
        }

        glp_prob *SimplificationContext::buildBase() const
        {
            constexpr auto infty = std::numeric_limits<double>::infinity(); // GLPK uses +/- inf for bounds
            if (timeout())                                                  // if we have timed out, we cannot build a base LP
                return nullptr;

            auto *lp = glp_create_prob(); // Create problem
            if (lp == nullptr)            // Failed to create problem
                return lp;

            const uint32_t nCol = _net->numberOfTransitions();              // Number of columns
            const int nRow = _net->numberOfPlaces();                        // Number of rows
            std::vector<int32_t> indir(std::max<uint32_t>(nCol, nRow) + 1); // Index array

            glp_add_cols(lp, nCol + 1); // Add columns
            glp_add_rows(lp, nRow + 1); // Add rows
            {
                std::vector<double> col = std::vector<double>(nRow + 1); // Column array. We add 1 to avoid 0 indexing
                for (size_t t = 0; t < _net->numberOfTransitions(); ++t)
                {
                    auto pre = _net->preset(t);   // Get the preset of the transition
                    auto post = _net->postset(t); // Get the postset of the transition
                    size_t l = 1;                 // Index in the column array
                    while (pre.first != pre.second ||
                           post.first != post.second) // While we have not reached the end of the preset or postset
                    {
                        if (pre.first == pre.second || (post.first != post.second && post.first->place < pre.first->place))
                        {
                            col[l] = post.first->tokens;      // Add the number of tokens in the postset
                            indir[l] = post.first->place + 1; // Add the place index
                            ++post.first;                     // Move to the next element in the postset
                        }
                        else if (post.first == post.second || (pre.first != pre.second && pre.first->place < post.first->place))
                        {
                            if (!pre.first->inhibitor) // If the place is not an inhibitor
                                col[l] = -(double)pre.first->tokens;
                            else
                                col[l] = 0;                  // If the place is an inhibitor, we do not add it to the column
                            indir[l] = pre.first->place + 1; // Add the place index
                            ++pre.first;
                        }
                        else
                        {
                            assert(pre.first->place == post.first->place);
                            if (!pre.first->inhibitor)
                                col[l] = (double)post.first->tokens - (double)pre.first->tokens;
                            else
                                col[l] = (double)post.first->tokens;
                            indir[l] = pre.first->place + 1;
                            ++pre.first;
                            ++post.first;
                        }
                        ++l;
                    }
                    glp_set_mat_col(lp, t + 1, l - 1, indir.data(), col.data()); // Set the column in the LP matrix
                    if (timeout())
                    {
                        std::cerr << "glpk: construction timeout" << std::endl;
                        glp_delete_prob(lp);
                        return nullptr;
                    }
                }
            }
            int rowno = 1;
            for (size_t p = 0; p < _net->numberOfPlaces(); p++)
            {
                glp_set_row_bnds(lp, rowno, GLP_LO, (0.0 - (double)_marking[p]), infty);
                ++rowno;
                if (timeout())
                {
                    std::cerr << "glpk: construction timeout" << std::endl;
                    glp_delete_prob(lp);
                    return nullptr;
                }
            }
            return lp;
        }
    }
}