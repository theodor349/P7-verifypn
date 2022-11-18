#include <cassert>
#include <cmath>
#include <glpk.h>
#include <fstream>

#include "PetriEngine/Simplification/LinearProgram.h"
#include "PetriEngine/Simplification/LPCache.h"
#include "PetriEngine/PQL/Contexts.h"

namespace PetriEngine
{
    namespace Simplification
    {
        using REAL = double;
        LinearProgram::~LinearProgram()
        {
        }

        LinearProgram::LinearProgram(Vector *vec, int constant, op_t op, LPCache *factory)
        {
            // TODO fix memory-management here!
            equation_t c;
            switch (op)
            {
            case Simplification::OP_LT:
                c.upper = constant - 1;
                break;
            case Simplification::OP_GT:
                c.lower = constant + 1;
                break;
            case Simplification::OP_LE:
                c.upper = constant;
                break;
            case Simplification::OP_GE:
                c.lower = constant;
                break;
            case Simplification::OP_EQ:
                c.lower = constant;
                c.upper = constant;
                break;
            default:
                // We ignore this operator for now by not adding any equation.
                // This is untested, however.
                assert(false);
            }
            c.row = vec;
            vec->inc();
            _equations.push_back(c);
        }

        constexpr auto infty = std::numeric_limits<REAL>::infinity();

        bool LinearProgram::isImpossible(const PQL::SimplificationContext &context, uint32_t solvetime)
        {
            bool use_ilp = true;
            auto net = context.net();

            if (_result != result_t::UKNOWN) // We already know the result
            {
                if (_result == result_t::IMPOSSIBLE) // We already know it is impossible
                    return _result == result_t::IMPOSSIBLE;
            }

            if (_equations.size() == 0 || context.timeout())
            { // No equations, or timeout
                return false;
            }

            const uint32_t nCol = net->numberOfTransitions();                // Number of columns (transitions)
            const uint32_t nRow = net->numberOfPlaces() + _equations.size(); // Number of rows (places + equations)

            std::vector<REAL> row = std::vector<REAL>(nCol + 1);  // Row to add to the matrix
            std::vector<int32_t> indir(std::max(nCol, nRow) + 1); // Indexes of the row
            for (size_t i = 0; i <= nCol; ++i)
                indir[i] = i;

            auto lp = context.makeBaseLP(); // Create a new LP
            if (lp == nullptr)              // If we could not create a new LP, we return false
                return false;

            int rowno = 1 + net->numberOfPlaces(); // The row number we are currently adding
            glp_add_rows(lp, _equations.size());   // Add the number of equations as rows
            for (const auto &eq : _equations)
            {                                                                // For each equation in the LP
                auto l = eq.row->write_indir(row, indir);                    // l is the number of elements in the row (excluding the constant)
                assert(!(std::isinf(eq.upper) && std::isinf(eq.lower)));     // We should not have infinite bounds
                glp_set_mat_row(lp, rowno, l - 1, indir.data(), row.data()); // lp is the LP, rowno is the row number, l-1 is the number of elements in the row, indir is the indexes of the row, and row is the row
                if (!std::isinf(eq.lower) && !std::isinf(eq.upper))          // If the lower and upper bound is not infinite
                {
                    if (eq.lower == eq.upper)                                    // If the lower and upper bound is the same
                        glp_set_row_bnds(lp, rowno, GLP_FX, eq.lower, eq.upper); // lp is the LP, rowno is the row number, GLP_FX is the type of bound, eq.lower is the lower bound, and eq.upper is the upper bound
                    else
                    {
                        if (eq.lower > eq.upper)
                        {
                            _result = result_t::IMPOSSIBLE;
                            glp_delete_prob(lp); // Delete the LP
                            return true;
                        }
                        glp_set_row_bnds(lp, rowno, GLP_DB, eq.lower, eq.upper); // GLP_DB is lb <= x <= ub whereas GLP_FX is x = c (lb = ub = c)
                    }
                }
                else if (std::isinf(eq.lower))                             // If the lower bound is infinite
                    glp_set_row_bnds(lp, rowno, GLP_UP, -infty, eq.upper); // GLP_UP is x <= ub where GLP_UP is -infty <= x <= ub
                else
                    glp_set_row_bnds(lp, rowno, GLP_LO, eq.lower, -infty);
                ++rowno;

                if (context.timeout())
                {
                    //                    std::cerr << "glpk: construction timeout" << std::endl;
                    glp_delete_prob(lp);
                    return false;
                }
            }

            // Set objective, kind and bounds
            for (size_t i = 1; i <= nCol; i++)
            {
                glp_set_obj_coef(lp, i, 0);                         // Set the objective coefficient of the i'th column to 0
                glp_set_col_kind(lp, i, use_ilp ? GLP_IV : GLP_CV); // Set the kind of the i'th column to GLP_IV if use_ilp is true, otherwise GLP_CV. GLP_IV is integer, GLP_CV is continuous
                glp_set_col_bnds(lp, i, GLP_LO, 0, infty);          // Set the bounds of the i'th column to 0 <= x <= infty
            }

            // use mip solver
            glp_set_obj_dir(lp, GLP_MIN); // GLP_MIN is minimize the objective
            auto stime = glp_time();      // Get the current time
            glp_smcp settings;            // Settings for the solver
            glp_init_smcp(&settings);     // Initialize the settings
            auto timeout = std::min(solvetime, context.getLpTimeout()) * 1000;
            settings.tm_lim = timeout;              // Set the time limit to timeout
            settings.presolve = GLP_OFF;            // Disable presolving
            settings.msg_lev = 0;                   // Disable messages
            auto result = glp_exact(lp, &settings); // The method to solve the LP

            // Simplex method is used in this case to find a feasible solution to the LP (if one exists) and to determine whether the LP is infeasible or unbounded
            if (result == GLP_ETMLIM)
            {
                _result = result_t::UKNOWN;
                // std::cerr << "glpk: timeout" << std::endl;
            }
            else if (result == 0) // If the result is 0, then the LP is feasible
            {
                auto status = glp_get_status(lp);
                if (status == GLP_OPT) // GLP_OPT - solution is integer feasible
                {
                    glp_iocp iset; // Settings for the ILP solver
                    glp_init_iocp(&iset);
                    iset.msg_lev = 0;
                    iset.tm_lim = std::max<uint32_t>(timeout - (stime - glp_time()), 1);
                    iset.presolve = GLP_OFF;
                    auto ires = glp_intopt(lp, &iset); // Solve the ILP using the branch and bound method
                    // The difference between Branch and bound method and simplex method is that the branch and bound method is used to find the optimal solution to the ILP whereas the simplex method is used to find a feasible solution to the LP
                    if (ires == GLP_ETMLIM) // GLP_ETMLIM - time limit exceeded
                    {
                        _result = result_t::UKNOWN;
                        // std::cerr << "glpk mip: timeout" << std::endl;
                    }
                    else if (ires == 0) // If 0, ILP is feasible
                    {
                        auto ist = glp_mip_status(lp); // Get the status of the ILP
                        if (ist == GLP_OPT || ist == GLP_FEAS || ist == GLP_UNBND)
                        {
                            _result = result_t::POSSIBLE;
                        }
                        else
                        {
                            _result = result_t::IMPOSSIBLE;
                        }
                    }
                }
                else if (status == GLP_FEAS || status == GLP_UNBND)
                {
                    _result = result_t::POSSIBLE;
                }
                else
                    _result = result_t::IMPOSSIBLE;
            }
            else if (result == GLP_ENOPFS || result == GLP_ENODFS || result == GLP_ENOFEAS) // GLP_ENOPFS - no primal feasible solution, GLP_ENODFS - no dual feasible solution, GLP_ENOFEAS - no primal or dual feasible solution
            {
                _result = result_t::IMPOSSIBLE;
            }

            if (_result == result_t::POSSIBLE)
            {
                std::vector<double> vect;
                for (size_t i = 1; i <= nCol; i++)
                {
                    double col_prim = glp_mip_col_val(lp, i); // Get the value of the i'th column in the optimal solution
                    if (col_prim > 0)
                    {
                        vect.push_back(col_prim);
                    }
                    auto x = 0.0;
                }
                auto x1 = vect.size();
                auto s = 0.0;
            }

            glp_delete_prob(lp); // Delete the LP

            return _result == result_t::IMPOSSIBLE; // Return true if the result is impossible, otherwise false (i.e. if the result is possible or unknown)
        }

        std::vector<std::pair<double, bool>> LinearProgram::bounds(const PQL::SimplificationContext &context, uint32_t solvetime, const std::vector<uint32_t> &places)
        {
            std::vector<std::pair<double, bool>> result(places.size() + 1, std::make_pair(std::numeric_limits<double>::infinity(), false)); // Initialize the result vector with the size of places + 1 and the value of the pair is infinity and false
            auto net = context.net();                                                                                                       // Get the net
            auto m0 = context.marking();                                                                                                    // Get the marking
            auto timeout = std::min(solvetime, context.getLpTimeout());                                                                     // Get the timeout

            const uint32_t nCol = net->numberOfTransitions();    // Get the number of transitions
            std::vector<REAL> row = std::vector<REAL>(nCol + 1); // Initialize the row vector with the size of nCol + 1. It will be used to set the coefficients of the constraints

            glp_smcp settings;                // Settings for the solver
            glp_init_smcp(&settings);         // Initialize the settings
            settings.tm_lim = timeout * 1000; // Set the time limit to timeout
            settings.presolve = GLP_OFF;      // Disable terminal output
            settings.msg_lev = 0;             // Disable messages

            for (size_t it = 0; it <= places.size(); ++it)
            {
                // we want to start with the overall bound, most important
                // Spend time on rest after
                auto stime = glp_time(); // Get the current time
                size_t pi;               // Place index
                if (it == 0)
                    pi = places.size(); // In first iteration pi is the size of places
                else
                    pi = it - 1; // In other iterations pi is decreased by 1

                if (context.timeout())
                {
                    return result;
                }
                // Create objective
                memset(row.data(), 0, sizeof(REAL) * net->numberOfTransitions() + 1); // Set the first nCol + 1 bytes of the block of memory pointed by row.data() to zero
                double p0 = 0;                                                        // p0 is the number of tokens in the place
                bool all_le_zero = true;
                bool all_zero = true;
                if (pi < places.size())
                {
                    auto tp = places[pi]; // Get the place.
                    p0 = m0[tp];          // Get the number of tokens in the place in the marking

                    // Iterate over all transitions and set the row to the weight of the transition
                    for (size_t t = 0; t < net->numberOfTransitions(); ++t)
                    {
                        row[1 + t] = net->outArc(t, tp); // Set the row to the weight of the transition
                        row[1 + t] -= net->inArc(tp, t); // Subtract the weight of the transition from the row
                        all_le_zero &= row[1 + t] <= 0;  // If the weight of the transition is less than or equal to zero, then all_le_zero is true
                        all_zero &= row[1 + t] == 0;     // If the weight of the transition is equal to zero, then all_zero is true
                    }
                }
                else
                {
                    for (size_t t = 0; t < net->numberOfTransitions(); ++t)
                    {
                        double cnt = 0; // cnt is the number of tokens in the place
                        for (auto tp : places)
                        {
                            cnt += net->outArc(t, tp); // Add the weight of the transition to cnt
                            cnt -= net->inArc(tp, t);  // Subtract the weight of the transition from cnt
                        }
                        row[1 + t] = cnt; // Set the row to cnt
                        all_le_zero &= row[1 + t] <= 0;
                        all_zero &= row[1 + t] == 0;
                    }
                    for (auto tp : places)
                        p0 += m0[tp]; // Add the number of tokens in the place to p0
                }

                if (all_le_zero)
                {
                    result[pi].first = p0;        // Set the first element is the pair to p0
                    result[pi].second = all_zero; // Set the second element of the pair to all_zero
                    if (pi == places.size())
                    {
                        return result;
                    }
                    continue;
                }

                // Set objective

                auto tmp_lp = context.makeBaseLP(); // Create a new LP
                if (tmp_lp == nullptr)
                    return result;

                // Max the objective
                glp_set_obj_dir(tmp_lp, GLP_MAX);
                // the function that is being maximized is the objective function

                for (size_t i = 1; i <= nCol; i++)
                {
                    glp_set_obj_coef(tmp_lp, i, row[i]);           // Set the objective coefficient of the i-th variable to row[i]
                    glp_set_col_kind(tmp_lp, i, GLP_IV);           // Set the kind of the i-th variable to GLP_IV
                    glp_set_col_bnds(tmp_lp, i, GLP_LO, 0, infty); // Set the bounds of the i-th variable to GLP_LO, 0 and infty
                }

                auto rs = glp_exact(tmp_lp, &settings); // glp_simplex solves the LP problem using the simplex method
                if (rs == GLP_ETMLIM)
                {
                    // std::cerr << "glpk: timeout" << std::endl;
                }
                else if (rs == 0)
                {
                    auto status = glp_get_status(tmp_lp);
                    if (status == GLP_OPT)
                    {
                        glp_iocp isettings;
                        glp_init_iocp(&isettings);
                        isettings.tm_lim = std::max<int>(((double)timeout * 1000) - (glp_time() - stime), 1);
                        isettings.msg_lev = 0;
                        isettings.presolve = GLP_OFF;
                        auto rs = glp_intopt(tmp_lp, &isettings); // glp_intopt: Solves an LP problem with the branch-and-bound method
                        if (rs == GLP_ETMLIM)
                        {
                            // std::cerr << "glpk mip: timeout" << std::endl;
                        }
                        else if (rs == 0)
                        {
                            auto status = glp_mip_status(tmp_lp);
                            if (status == GLP_OPT)
                            {
                                auto org = p0 + glp_mip_obj_val(tmp_lp);
                                result[pi].first = std::round(org);
                                result[pi].second = all_zero;
                            }
                            else if (status != GLP_UNBND && status != GLP_FEAS)
                            {
                                result[pi].first = p0;
                                result[pi].second = all_zero;
                            }
                        }
                    }
                    else if (status == GLP_INFEAS || status == GLP_NOFEAS || status == GLP_UNDEF)
                    {
                        result[pi].first = p0;
                        result[pi].second = all_zero;
                    }
                }
                else if (rs == GLP_ENOPFS || rs == GLP_ENODFS || rs == GLP_ENOFEAS)
                {
                    result[pi].first = p0;
                    result[pi].second = all_zero;
                }
                glp_erase_prob(tmp_lp);
                if (pi == places.size() && result[places.size()].first >= p0)
                {
                    return result;
                }
                if (pi == places.size() && places.size() == 1)
                {
                    result[0] = result[1];
                    return result;
                }
            }
            return result;
        }

        void LinearProgram::make_union(const LinearProgram &other)
        {
            if (_result == IMPOSSIBLE || other._result == IMPOSSIBLE)
            {
                _result = IMPOSSIBLE;
                _equations.clear();
                assert(false);
                return;
            }

            auto it1 = _equations.begin();
            auto it2 = other._equations.begin();

            while (it1 != _equations.end() && it2 != other._equations.end())
            {
                if (it1->row < it2->row)
                {
                    ++it1;
                }
                else if (it2->row < it1->row)
                {
                    it1 = _equations.insert(it1, *it2);
                    ++it2;
                    ++it1;
                }
                else
                {
                    equation_t &n = *it1;
                    n.lower = std::max(n.lower, it2->lower);
                    n.upper = std::min(n.upper, it2->upper);
                    /*if(n.upper < n.lower)
                    {
                        _result = result_t::IMPOSSIBLE;
                        _equations.clear();
                        return;
                    }*/
                    ++it1;
                    ++it2;
                }
            }

            if (it2 != other._equations.end())
                _equations.insert(_equations.end(), it2, other._equations.end());
        }
    }
}
