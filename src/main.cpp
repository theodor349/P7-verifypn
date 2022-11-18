/* TAPAAL untimed verification engine verifypn
 * Copyright (C) 2011-2021  Jonas Finnemann Jensen <jopsen@gmail.com>,
 *                          Thomas Søndersø Nielsen <primogens@gmail.com>,
 *                          Lars Kærlund Østergaard <larsko@gmail.com>,
 *                          Jiri Srba <srba.jiri@gmail.com>,
 *                          Peter Gjøl Jensen <root@petergjoel.dk>
 *
 * CTL Extension
 *                          Peter Fogh <peter.f1992@gmail.com>
 *                          Isabella Kaufmann <bellakaufmann93@gmail.com>
 *                          Tobias Skovgaard Jepsen <tobiasj1991@gmail.com>
 *                          Lasse Steen Jensen <lassjen88@gmail.com>
 *                          Søren Moss Nielsen <soren_moss@mac.com>
 *                          Samuel Pastva <daemontus@gmail.com>
 *                          Jiri Srba <srba.jiri@gmail.com>
 *
 * Stubborn sets, query simplification, siphon-trap property
 *                          Frederik Meyer Boenneland <sadpantz@gmail.com>
 *                          Jakob Dyhr <jakobdyhr@gmail.com>
 *                          Peter Gjøl Jensen <root@petergjoel.dk>
 *                          Mads Johannsen <mads_johannsen@yahoo.com>
 *                          Jiri Srba <srba.jiri@gmail.com>
 *
 * LTL Extension
 *                          Nikolaj Jensen Ulrik <nikolaj@njulrik.dk>
 *                          Simon Mejlby Virenfeldt <simon@simwir.dk>
 *
 * Color Extension
 *                          Alexander Bilgram <alexander@bilgram.dk>
 *                          Peter Haar Taankvist <ptaankvist@gmail.com>
 *                          Thomas Pedersen <thomas.pedersen@stofanet.dk>
 *                          Andreas H. Klostergaard
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

#include <PetriEngine/Colored/PnmlWriter.h>
#include "VerifyPN.h"
#include "PetriEngine/Synthesis/SimpleSynthesis.h"
#include "LTL/LTLSearch.h"
#include "PetriEngine/PQL/PQL.h"

using namespace PetriEngine;
using namespace PetriEngine::PQL;
using namespace PetriEngine::Reachability;

int main(int argc, const char **argv)
{
    shared_string_set string_set; //<-- used for de-duplicating names of places/transitions
    try
    {
        options_t options;
        if (options.parse(argc, argv)) // if options were --help or --version
            return to_underlying(ReturnValue::SuccessCode);

        if (options.printstatistics)
        {
            std::cout << std::endl
                      << "Parameters: ";
            for (int i = 1; i < argc; i++)
            {
                std::cout << argv[i] << " ";
            }
            std::cout << std::endl;
        }
        options.print();

        ColoredPetriNetBuilder cpnBuilder(string_set);
        try
        {
            cpnBuilder.parse_model(options.modelfile);
            options.isCPN = cpnBuilder.isColored(); // TODO: this is really nasty, should be moved in a refactor
        }
        catch (const base_error &err)
        {
            throw base_error("CANNOT_COMPUTE\nError parsing the model\n", err.what());
        }

        if (!options.model_col_out_file.empty() && cpnBuilder.hasPartition())
        {
            std::cerr << "Cannot write colored PNML as the original net has partitions. Not supported (yet)" << std::endl;
            return to_underlying(ReturnValue::UnknownCode);
        }

        if (options.cpnOverApprox && !cpnBuilder.isColored())
        {
            std::cerr << "CPN OverApproximation is only usable on colored models" << std::endl;
            return to_underlying(ReturnValue::UnknownCode);
        }

        if (options.printstatistics)
        {
            std::cout << "Finished parsing model" << std::endl;
        }

        //----------------------- Parse Query -----------------------//
        std::vector<std::string> querynames;
        auto ctlStarQueries = readQueries(string_set, options, querynames);
        auto queries = options.logic == TemporalLogic::CTL
                           ? getCTLQueries(ctlStarQueries)
                           : getLTLQueries(ctlStarQueries);

        if (options.printstatistics && options.queryReductionTimeout > 0)
        {
            negstat_t stats;
            std::cout << "RWSTATS LEGEND:";
            stats.printRules(std::cout);
            std::cout << std::endl;
        }

        if (cpnBuilder.isColored())
        {
            negstat_t stats;
            EvaluationContext context(nullptr, nullptr);
            for (ssize_t qid = queries.size() - 1; qid >= 0; --qid)
            {
                queries[qid] = pushNegation(queries[qid], stats, context, false, false, false);
                if (options.printstatistics)
                {
                    std::cout << "\nQuery before expansion and reduction: ";
                    queries[qid]->toString(std::cout);
                    std::cout << std::endl;

                    std::cout << "RWSTATS COLORED PRE:";
                    stats.print(std::cout);
                    std::cout << std::endl;
                }
            }
        }

        if (options.cpnOverApprox)
        {
            for (ssize_t qid = queries.size() - 1; qid >= 0; --qid)
            {
                negstat_t stats;
                EvaluationContext context(nullptr, nullptr);
                auto q = pushNegation(queries[qid], stats, context, false, false, false);
                if (!PetriEngine::PQL::isReachability(q) || PetriEngine::PQL::isLoopSensitive(q) ||
                    stats.negated_fireability)
                {
                    std::cerr
                        << "Warning: CPN OverApproximation is only available for Reachability queries without deadlock, negated fireability and UpperBounds, skipping "
                        << querynames[qid] << std::endl;
                    queries.erase(queries.begin() + qid);
                    querynames.erase(querynames.begin() + qid);
                }
            }
        }

        std::stringstream ss;
        std::ostream &out = options.printstatistics ? std::cout : ss;
        reduceColored(cpnBuilder, queries, options.logic, options.colReductionTimeout, out, options.enablecolreduction, options.colreductions);

        if (options.model_col_out_file.size() > 0)
        {
            std::fstream file;
            file.open(options.model_col_out_file, std::ios::out);
            PetriEngine::Colored::PnmlWriter writer(cpnBuilder, file);
            writer.toColPNML();
        }

        if (!options.doUnfolding)
        {
            return 0;
        }

        auto [builder, transition_names, place_names] = unfold(cpnBuilder,
                                                               options.computePartition, options.symmetricVariables,
                                                               options.computeCFP, out,
                                                               options.partitionTimeout, options.max_intervals, options.max_intervals_reduced,
                                                               options.intervalTimeout, options.cpnOverApprox);

        builder.sort();
        std::vector<ResultPrinter::Result> results(queries.size(), ResultPrinter::Result::Unknown);
        ResultPrinter printer(&builder, &options, querynames);

        if (options.unfolded_out_file.size() > 0)
        {
            outputNet(builder, options.unfolded_out_file);
        }

        //----------------------- Query Simplification -----------------------//
        bool alldone = options.queryReductionTimeout > 0;
        PetriNetBuilder b2(builder);
        std::set<size_t> initial_marking_solved;
        size_t initial_size = 0;
        ResultPrinter p2(&b2, &options, querynames);
        {
            std::unique_ptr<PetriNet> qnet(b2.makePetriNet(false));
            std::unique_ptr<MarkVal[]> qm0(qnet->makeInitialMarking());
            for (size_t i = 0; i < qnet->numberOfPlaces(); ++i)
                initial_size += qm0[i];

            if (queries.empty() && options.cpnOverApprox)
            {
                std::cerr << "WARNING: Could not run CPN over-approximation on any queries, terminating." << std::endl;
                std::exit(0);
            }

            if (queries.empty() ||
                contextAnalysis(cpnBuilder.isColored() && !options.cpnOverApprox, transition_names, place_names, b2, qnet.get(), queries) != ReturnValue::ContinueCode)
            {
                throw base_error("Could not analyze the queries");
            }

            if (options.unfold_query_out_file.size() > 0)
            {
                outputCompactQueries(builder, queries, querynames, options.unfold_query_out_file, options.keep_solved);
            }

            {
                EvaluationContext context(qm0.get(), qnet.get());
                for (size_t i = 0; i < queries.size(); ++i)
                {
                    ContainsFireabilityVisitor has_fireability;
                    Visitor::visit(has_fireability, queries[i]);
                    if (has_fireability.getReturnValue() && options.cpnOverApprox)
                        continue;
                    if (containsUpperBounds(queries[i]))
                        continue;
                    auto r = PQL::evaluate(queries[i].get(), context);
                    if (r == Condition::RFALSE)
                    {
                        queries[i] = BooleanCondition::FALSE_CONSTANT;
                        initial_marking_solved.emplace(i);
                    }
                    else if (r == Condition::RTRUE)
                    {
                        queries[i] = BooleanCondition::TRUE_CONSTANT;
                        initial_marking_solved.emplace(i);
                    }
                }
            }

            // simplification. We always want to do negation-push and initial marking check.
            simplify_queries(qm0.get(), qnet.get(), queries, options, std::cout);

            if (options.query_out_file.size() > 0)
            {
                outputQueries(builder, queries, querynames, options.query_out_file, options.binary_query_io, options.keep_solved);
            }
            if (!options.statespaceexploration)
            {
                for (size_t i = 0; i < queries.size(); ++i)
                {
                    if (queries[i]->isTriviallyTrue())
                    {
                        if (initial_marking_solved.count(i) > 0 && options.trace != TraceLevel::None)
                        {
                            // we misuse the implementation to make sure we print the empty-trace
                            // when the initial marking is sufficient.
                            Structures::StateSet tmp(*qnet, 0);
                            results[i] = p2.handle(i, queries[i].get(), ResultPrinter::Satisfied, nullptr,
                                                   0, 1, 1, initial_size, &tmp, 0, qm0.get())
                                             .first;
                        }
                        else
                            results[i] = p2.handle(i, queries[i].get(), ResultPrinter::Satisfied).first;
                        if (results[i] == ResultPrinter::Ignore && options.printstatistics)
                        {
                            std::cout << "Unable to decide if query is satisfied." << std::endl
                                      << std::endl;
                        }
                        else if (options.printstatistics)
                        {
                            std::cout << "Query solved by Query Simplification.\n"
                                      << std::endl;
                        }
                    }
                    else if (queries[i]->isTriviallyFalse())
                    {
                        if (initial_marking_solved.count(i) > 0 && options.trace != TraceLevel::None)
                        {
                            // we misuse the implementation to make sure we print the empty-trace
                            // when the initial marking is sufficient.
                            Structures::StateSet tmp(*qnet, 0);
                            // we are tricking the printer into printing the trace here.
                            // TODO fix, remove setInvariant
                            // also we make a new FALSE object here to avoid sideeffects.
                            queries[i] = std::make_shared<BooleanCondition>(false);
                            queries[i]->setInvariant(true);
                            results[i] = p2.handle(i, queries[i].get(), ResultPrinter::Satisfied, nullptr,
                                                   0, 1, 1, initial_size, &tmp, 0, qm0.get())
                                             .first;
                        }
                        else
                            results[i] = p2.handle(i, queries[i].get(), ResultPrinter::NotSatisfied).first;
                        if (results[i] == ResultPrinter::Ignore && options.printstatistics)
                        {
                            std::cout << "Unable to decide if query is satisfied." << std::endl
                                      << std::endl;
                        }
                        else if (options.printstatistics)
                        {
                            std::cout << "Query solved by Query Simplification.\n"
                                      << std::endl;
                        }
                    }
                    else if (options.strategy == Strategy::OverApprox)
                    {
                        results[i] = p2.handle(i, queries[i].get(), ResultPrinter::Unknown).first;
                        if (options.printstatistics)
                        {
                            std::cout << "Unable to decide if query is satisfied." << std::endl
                                      << std::endl;
                        }
                    }
                    else if (options.noreach || !PetriEngine::PQL::isReachability(queries[i]))
                    {
                        if (std::dynamic_pointer_cast<PQL::ControlCondition>(queries[i]))
                            results[i] = ResultPrinter::Synthesis;
                        else
                            results[i] = options.logic == TemporalLogic::CTL ? ResultPrinter::CTL : ResultPrinter::LTL;
                        alldone = false;
                    }
                    else
                    {
                        alldone = false;
                    }
                }

                if (alldone && options.model_out_file.size() == 0)
                    return to_underlying(ReturnValue::SuccessCode);
            }
        }

        options.queryReductionTimeout = 0;

        //--------------------- Apply Net Reduction ---------------//

        builder.freezeOriginalSize();
        if (options.enablereduction > 0)
        {
            // Compute structural reductions
            builder.startTimer();
            builder.reduce(queries, results, options.enablereduction, options.trace != TraceLevel::None, nullptr,
                           options.reductionTimeout, options.reductions);
            printer.setReducer(builder.getReducer());
        }

        printStats(builder, options);

        auto net = std::unique_ptr<PetriNet>(builder.makePetriNet());

        // bool isImpossible(PetriNet *net, equation_t equation, MarkVal *marking, uint32_t solvetime)
        // isImpossible(&net, queries[0], net->_initialMarking());

        if (options.model_out_file.size() > 0)
        {
            std::fstream file;
            file.open(options.model_out_file, std::ios::out);
            net->toXML(file);
        }

        if (alldone)
            return to_underlying(ReturnValue::SuccessCode);

        if (options.replay_trace)
        {
            if (contextAnalysis(cpnBuilder.isColored() && !options.cpnOverApprox, transition_names, place_names, builder, net.get(), queries) != ReturnValue::ContinueCode)
            {
                throw base_error("Fatal error assigning indexes");
            }
            std::ifstream replay_file(options.replay_file, std::ifstream::in);
            PetriEngine::TraceReplay replay{replay_file, net.get(), options};
            for (size_t i = 0; i < queries.size(); ++i)
            {
                if (results[i] == ResultPrinter::Unknown || results[i] == ResultPrinter::CTL ||
                    results[i] == ResultPrinter::LTL)
                    replay.replay(net.get(), queries[i]);
            }
            return to_underlying(ReturnValue::SuccessCode);
        }

        if (options.strategy == Strategy::OverApprox)
        {
            return to_underlying(ReturnValue::SuccessCode);
        }

        if (options.doVerification)
        {

            auto verifStart = std::chrono::high_resolution_clock::now();
            // When this ptr goes out of scope it will print the time spent during verification
            std::shared_ptr<void> defer(nullptr, [&verifStart](...)
                                        {
                auto verifEnd = std::chrono::high_resolution_clock::now();
                auto diff = std::chrono::duration_cast<std::chrono::microseconds>(verifEnd - verifStart).count() / 1000000.0;
                std::cout << std::setprecision(6) << "Spent " << diff << " on verification" << std::endl; });

            //----------------------- Verify CTL queries -----------------------//
            std::vector<size_t> ctl_ids;
            std::vector<size_t> ltl_ids;
            std::vector<size_t> synth_ids;
            for (size_t i = 0; i < queries.size(); ++i)
            {
                if (results[i] == ResultPrinter::CTL)
                {
                    ctl_ids.push_back(i);
                }
                else if (results[i] == ResultPrinter::LTL)
                {
                    ltl_ids.push_back(i);
                }
                else if (results[i] == ResultPrinter::Synthesis)
                {
                    synth_ids.push_back(i);
                }
            }

            if (options.replay_trace)
            {
                if (contextAnalysis(cpnBuilder.isColored() && !options.cpnOverApprox, transition_names, place_names, builder, net.get(), queries) != ReturnValue::ContinueCode)
                {
                    throw base_error("Fatal error assigning indexes");
                }
                std::ifstream replay_file(options.replay_file, std::ifstream::in);
                PetriEngine::TraceReplay replay{replay_file, net.get(), options};
                for (int i : ltl_ids)
                {
                    replay.replay(net.get(), queries[i]);
                }
                return to_underlying(ReturnValue::SuccessCode);
            }

            // Assign indexes
            if (queries.empty() ||
                contextAnalysis(cpnBuilder.isColored() && !options.cpnOverApprox, transition_names, place_names, builder, net.get(), queries) != ReturnValue::ContinueCode)
            {
                throw base_error("An error occurred while assigning indexes");
            }

            if (!ctl_ids.empty())
            {
                options.usedctl = true;
                auto reachabilityStrategy = options.strategy;

                if (options.strategy == Strategy::DEFAULT)
                    options.strategy = Strategy::DFS;
                auto v = CTLMain(net.get(),
                                 options.ctlalgorithm,
                                 options.strategy,
                                 options.printstatistics,
                                 options.stubbornreduction,
                                 querynames,
                                 queries,
                                 ctl_ids,
                                 options);

                if (std::find(results.begin(), results.end(), ResultPrinter::Unknown) == results.end())
                {
                    return to_underlying(v);
                }
                // go back to previous strategy if the program continues
                options.strategy = reachabilityStrategy;
            }

            //----------------------- Verify LTL queries -----------------------//

            if (!ltl_ids.empty() && options.ltlalgorithm != LTL::Algorithm::None)
            {
                options.usedltl = true;

                for (auto qid : ltl_ids)
                {
                    LTL::LTLSearch search(*net, queries[qid], options.buchiOptimization, options.ltl_compress_aps);
                    auto res = search.solve(options.trace != TraceLevel::None, options.kbound,
                                            options.ltlalgorithm, options.stubbornreduction ? options.ltl_por : LTL::LTLPartialOrder::None,
                                            options.strategy, options.ltlHeuristic, options.ltluseweak, options.seed_offset);

                    if (options.printstatistics)
                        search.print_stats(std::cout);

                    std::cout << "FORMULA " << querynames[qid]
                              << (res ? " TRUE" : " FALSE") << " TECHNIQUES EXPLICIT "
                              << LTL::to_string(options.ltlalgorithm)
                              << (search.is_weak() ? " WEAK_SKIP" : "")
                              << (search.used_partial_order() != LTL::LTLPartialOrder::None ? " STUBBORN" : "")
                              << (search.used_partial_order() == LTL::LTLPartialOrder::Visible ? " CLASSIC_STUB" : "")
                              << (search.used_partial_order() == LTL::LTLPartialOrder::Automaton ? " AUT_STUB" : "")
                              << (search.used_partial_order() == LTL::LTLPartialOrder::Liebke ? " LIEBKE_STUB" : "");
                    auto heur = search.heuristic_type();
                    if (!heur.empty())
                        std::cout << " HEURISTIC " << heur;
                    std::cout << " OPTIM-" << to_underlying(options.buchiOptimization) << std::endl;

                    std::cout << "\nQuery index " << qid << " was solved\n";
                    std::cout << "Query is " << (res ? "" : "NOT ") << "satisfied." << std::endl;

                    if (options.trace != TraceLevel::None)
                        search.print_trace(std::cerr, *builder.getReducer());
                }

                if (std::find(results.begin(), results.end(), ResultPrinter::Unknown) == results.end())
                {
                    return to_underlying(ReturnValue::SuccessCode);
                }
            }

            for (auto i : synth_ids)
            {
                Synthesis::SimpleSynthesis strategy(*net, *queries[i], options.kbound);

                std::ostream *strategy_out = nullptr;

                results[i] = strategy.synthesize(options.strategy, options.stubbornreduction, false);

                strategy.result().print(querynames[i], options.printstatistics, i, options, std::cout);

                if (options.strategy_output == "_")
                    strategy_out = &std::cout;
                else if (options.strategy_output.size() > 0)
                    strategy_out = new std::ofstream(options.strategy_output);

                if (strategy_out != nullptr)
                    strategy.print_strategy(*strategy_out);

                if (strategy_out != nullptr && strategy_out != &std::cout)
                    delete strategy_out;
                if (std::find(results.begin(), results.end(), ResultPrinter::Unknown) == results.end())
                {
                    return to_underlying(ReturnValue::SuccessCode);
                }
            }

            //----------------------- Siphon Trap ------------------------//

            if (options.siphontrapTimeout > 0)
            {
                for (uint32_t i = 0; i < results.size(); i++)
                {
                    bool isDeadlockQuery = std::dynamic_pointer_cast<DeadlockCondition>(queries[i]) != nullptr;

                    if (results[i] == ResultPrinter::Unknown && isDeadlockQuery)
                    {
                        STSolver stSolver(printer, *net, queries[i].get(), options.siphonDepth);
                        stSolver.solve(options.siphontrapTimeout);
                        results[i] = stSolver.printResult();
                        if (results[i] != Reachability::ResultPrinter::Unknown && options.printstatistics)
                        {
                            std::cout << "Query solved by Siphon-Trap Analysis." << std::endl
                                      << std::endl;
                        }
                    }
                }

                if (std::find(results.begin(), results.end(), ResultPrinter::Unknown) == results.end())
                {
                    return to_underlying(ReturnValue::SuccessCode);
                }
            }
            options.siphontrapTimeout = 0;

            //----------------------- Reachability -----------------------//

            // Change default place-holder to default strategy
            if (options.strategy == Strategy::DEFAULT)
                options.strategy = Strategy::HEUR;

            // remove the prefix EF/AF (LEGACY, should not be handled here)
            for (uint32_t i = 0; i < results.size(); ++i)
            {
                if (results[i] == ResultPrinter::Unknown)
                    queries[i] = prepareForReachability(queries[i]);
            }
            if (options.tar && net->numberOfPlaces() > 0)
            {
                // Create reachability search strategy
                TarResultPrinter tar_printer(printer);
                TARReachabilitySearch strategy(tar_printer, *net, builder.getReducer(), options.kbound);

                // Change default place-holder to default strategy
                fprintf(stdout, "Search strategy option was ignored as the TAR engine is called.\n");
                options.strategy = Strategy::DFS;

                // Reachability search
                strategy.reachable(queries, results,
                                   options.printstatistics,
                                   options.trace != TraceLevel::None);
            }
            else
            {
                ReachabilitySearch strategy(*net, printer, options.kbound);

                // Change default place-holder to default strategy
                if (options.strategy == Strategy::DEFAULT)
                    options.strategy = Strategy::HEUR;

                // Reachability search
                strategy.reachable(queries, results,
                                   options.strategy,
                                   options.stubbornreduction,
                                   options.statespaceexploration,
                                   options.printstatistics,
                                   options.trace != TraceLevel::None,
                                   options.seed());
            }
        }
    }
    catch (base_error &e)
    {
        std::cerr << "ERROR: " << e.what() << std::endl;
        std::exit(-1);
    }

    return to_underlying(ReturnValue::SuccessCode);
}

glp_prob *buildBase(PetriNet *net, MarkVal *marking)
{
    constexpr auto infty = std::numeric_limits<double>::infinity(); // GLPK uses +/- inf for bounds

    auto *lp = glp_create_prob(); // Create problem
    if (lp == nullptr)            // Failed to create problem
        return lp;

    const uint32_t nCol = net->numberOfTransitions();               // Number of columns
    const int nRow = net->numberOfPlaces();                         // Number of rows
    std::vector<int32_t> indir(std::max<uint32_t>(nCol, nRow) + 1); // Index array

    glp_add_cols(lp, nCol + 1); // Add columns
    glp_add_rows(lp, nRow + 1); // Add rows
    {
        std::vector<double> col = std::vector<double>(nRow + 1); // Column array. We add 1 to avoid 0 indexing
        for (size_t t = 0; t < net->numberOfTransitions(); ++t)
        {
            auto pre = net->preset(t);   // Get the preset of the transition
            auto post = net->postset(t); // Get the postset of the transition
            size_t l = 1;                // Index in the column array
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
        }
    }
    int rowno = 1;
    for (size_t p = 0; p < net->numberOfPlaces(); p++)
    {
        glp_set_row_bnds(lp, rowno, GLP_LO, (0.0 - (double)marking[p]), infty);
        ++rowno;
    }
    return lp;
}

bool isImpossible(PetriNet *net, equation_t equation, MarkVal *marking)
{
    constexpr auto infty = std::numeric_limits<double>::infinity();
    int result;

    const uint32_t nCol = net->numberOfTransitions();
    const uint32_t nRow = net->numberOfPlaces() + 1;

    std::vector<double> row = std::vector<double>(nCol + 1); // Row to add to the matrix
    std::vector<int32_t> indir(std::max(nCol, nRow) + 1);    // Indexes of the row
    for (size_t i = 0; i <= nCol; ++i)
        indir[i] = i;

    auto *lp = glp_create_prob();
    auto base_lp = buildBase(net, marking);

    glp_copy_prob(lp, base_lp, GLP_OFF);
    if (lp == nullptr) // If we could not create a new LP, we return false
        return false;

    int rowno = 1 + net->numberOfPlaces();
    glp_add_rows(lp, 1);
    auto l = equation.row->write_indir(row, indir);                      // l is the number of elements in the row (excluding the constant)
    assert(!(std::isinf(equation.upper) && std::isinf(equation.lower))); // We should not have infinite bounds
    glp_set_mat_row(lp, rowno, l - 1, indir.data(), row.data());         // lp is the LP, rowno is the row number, l-1 is the number of elements in the row, indir is the indexes of the row, and row is the row
    if (!std::isinf(equation.lower) && !std::isinf(equation.upper))      // If the lower and upper bound is not infinite
    {
        if (equation.lower == equation.upper)                                    // If the lower and upper bound is the same
            glp_set_row_bnds(lp, rowno, GLP_FX, equation.lower, equation.upper); // lp is the LP, rowno is the row number, GLP_FX is the type of bound, eq.lower is the lower bound, and eq.upper is the upper bound
        else
        {
            if (equation.lower > equation.upper)
            {
                result = 1;
                glp_delete_prob(lp); // Delete the LP
                return true;
            }
            glp_set_row_bnds(lp, rowno, GLP_DB, equation.lower, equation.upper); // GLP_DB is lb <= x <= ub whereas GLP_FX is x = c (lb = ub = c)
        }
    }
    else if (std::isinf(equation.lower))                             // If the lower bound is infinite
        glp_set_row_bnds(lp, rowno, GLP_UP, -infty, equation.upper); // GLP_UP is x <= ub where GLP_UP is -infty <= x <= ub
    else
        glp_set_row_bnds(lp, rowno, GLP_LO, equation.lower, -infty);
    ++rowno;

    // Set objective, kind and bounds
    for (size_t i = 1; i <= nCol; i++)
    {
        glp_set_obj_coef(lp, i, 0);                      // Set the objective coefficient of the i'th column to 0
        glp_set_col_kind(lp, i, true ? GLP_IV : GLP_CV); // Set the kind of the i'th column to GLP_IV if use_ilp is true, otherwise GLP_CV. GLP_IV is integer, GLP_CV is continuous
        glp_set_col_bnds(lp, i, GLP_LO, 0, infty);       // Set the bounds of the i'th column to 0 <= x <= infty
    }

    // Use MIP Solver
    glp_set_obj_dir(lp, GLP_MIN);                 // GLP_MIN is minimize the objective
    glp_smcp settings;                            // Settings for the solver
    glp_init_smcp(&settings);                     // Initialize the settings
    settings.presolve = GLP_OFF;                  // Disable presolving
    settings.msg_lev = 0;                         // Disable messages
    auto result_exact = glp_exact(lp, &settings); // The method to solve the LP

    if (result_exact == GLP_ETMLIM)
    {
        result = 0;
        // std::cerr << "glpk: timeout" << std::endl;
    }
    else if (result_exact == 0) // If the result is 0, then the LP is feasible
    {
        auto status = glp_get_status(lp);
        if (status == GLP_OPT) // GLP_OPT - solution is integer feasible
        {
            glp_iocp iset; // Settings for the ILP solver
            glp_init_iocp(&iset);
            iset.msg_lev = 0;
            iset.presolve = GLP_OFF;
            auto ires = glp_intopt(lp, &iset); // Solve the ILP using the branch and bound method
            // The difference between Branch and bound method and simplex method is that the branch and bound method is used to find the optimal solution to the ILP whereas the simplex method is used to find a feasible solution to the LP
            if (ires == GLP_ETMLIM) // GLP_ETMLIM - time limit exceeded
            {
                result = 0;
                // std::cerr << "glpk mip: timeout" << std::endl;
            }
            else if (ires == 0) // If 0, ILP is feasible
            {
                auto ist = glp_mip_status(lp); // Get the status of the ILP
                if (ist == GLP_OPT || ist == GLP_FEAS || ist == GLP_UNBND)
                {
                    result = 2;
                }
                else
                {
                    result = 1;
                }
            }
        }
        else if (status == GLP_FEAS || status == GLP_UNBND)
        {
            result = 2;
        }
        else
            result = 1;
    }
    else if (result_exact == GLP_ENOPFS || result_exact == GLP_ENODFS || result_exact == GLP_ENOFEAS) // GLP_ENOPFS - no primal feasible solution, GLP_ENODFS - no dual feasible solution, GLP_ENOFEAS - no primal or dual feasible solution
    {
        result = 1;
    }

    if (result == 2)
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

    return result == 1; // Return true if the result is impossible, otherwise false (i.e. if the result is possible or unknown)
}