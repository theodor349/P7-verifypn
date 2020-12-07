/*
 * File:   ColoredPetriNetBuilder.cpp
 * Author: Klostergaard
 * 
 * Created on 17. februar 2018, 16:25
 */

#include "PetriEngine/Colored/ColoredPetriNetBuilder.h"
#include <chrono>

namespace PetriEngine {
    ColoredPetriNetBuilder::ColoredPetriNetBuilder() {
    }

    ColoredPetriNetBuilder::ColoredPetriNetBuilder(const ColoredPetriNetBuilder& orig) {
    }

    ColoredPetriNetBuilder::~ColoredPetriNetBuilder() {
    }

    void ColoredPetriNetBuilder::addPlace(const std::string& name, int tokens, double x, double y) {
        if (!_isColored) {
            _ptBuilder.addPlace(name, tokens, x, y);
        }
    }

    void ColoredPetriNetBuilder::addPlace(const std::string& name, Colored::ColorType* type, Colored::Multiset&& tokens, double x, double y) {
        if(_placenames.count(name) == 0)
        {
            uint32_t next = _placenames.size();
            _places.emplace_back(Colored::Place {name, type, tokens});
            _placenames[name] = next;

            //set up place color fix points and initialize queue
            if (!tokens.empty()) {
                _placeFixpointQueue.emplace_back(next);
            }

            Reachability::intervalTuple_t placeConstraints;
            Colored::ColorFixpoint colorFixpoint = {placeConstraints, !tokens.empty(), (uint32_t) type->productSize()};

            if(tokens.size() == type->size()){
                colorFixpoint.constraints.addInterval(type->getFullInterval());
            } else {
                uint32_t index = 0;
                for (auto colorPair : tokens) {
                    Reachability::interval_t tokenConstraints;
                    colorPair.first->getColorConstraints(&tokenConstraints, &index);

                    colorFixpoint.constraints.addInterval(tokenConstraints);
                    index = 0;
                }
                colorFixpoint.constraints.mergeIntervals();
            }
         
            _placeColorFixpoints.push_back(colorFixpoint);            
        }
    }

    void ColoredPetriNetBuilder::addTransition(const std::string& name, double x, double y) {
        if (!_isColored) {
            _ptBuilder.addTransition(name, x, y);
        }
    }

    void ColoredPetriNetBuilder::addTransition(const std::string& name, const Colored::GuardExpression_ptr& guard, double x, double y) {
        if(_transitionnames.count(name) == 0)
        {
            uint32_t next = _transitionnames.size();
            _transitions.emplace_back(Colored::Transition {name, guard});
            _transitionnames[name] = next;
        }
    }

    void ColoredPetriNetBuilder::addInputArc(const std::string& place, const std::string& transition, bool inhibitor, int weight) {
        if (!_isColored) {
            _ptBuilder.addInputArc(place, transition, inhibitor, weight);
        }
    }

    void ColoredPetriNetBuilder::addInputArc(const std::string& place, const std::string& transition, const Colored::ArcExpression_ptr& expr) {
        addArc(place, transition, expr, true);
    }

    void ColoredPetriNetBuilder::addOutputArc(const std::string& transition, const std::string& place, int weight) {
        if (!_isColored) {
            _ptBuilder.addOutputArc(transition, place, weight);
        }
    }

    void ColoredPetriNetBuilder::addOutputArc(const std::string& transition, const std::string& place, const Colored::ArcExpression_ptr& expr) {
        addArc(place, transition, expr, false);
    }

    void ColoredPetriNetBuilder::addArc(const std::string& place, const std::string& transition, const Colored::ArcExpression_ptr& expr, bool input) {
        if(_transitionnames.count(transition) == 0)
        {
            std::cout << "Transition '" << transition << "' not found. Adding it." << std::endl;
            addTransition(transition,0.0,0.0);
        }
        if(_placenames.count(place) == 0)
        {
            std::cout << "Place '" << place << "' not found. Adding it." << std::endl;
            addPlace(place,0,0,0);
        }
        uint32_t p = _placenames[place];
        uint32_t t = _transitionnames[transition];

        assert(t < _transitions.size());
        assert(p < _places.size());

        if (input) _placePostTransitionMap[p].emplace_back(t);

        Colored::Arc arc;
        arc.place = p;
        arc.transition = t;
        assert(expr != nullptr);
        arc.expr = std::move(expr);
        arc.input = input;
        input? _transitions[t].input_arcs.push_back(std::move(arc)): _transitions[t].output_arcs.push_back(std::move(arc));
    }

    void ColoredPetriNetBuilder::addColorType(const std::string& id, Colored::ColorType* type) {
        _colors[id] = type;
    }

    void ColoredPetriNetBuilder::sort() {

    }

    void ColoredPetriNetBuilder::printPlaceTable() {
        for (auto place: _places) {
            auto placeID = _placenames[place.name];
            auto placeColorFixpoint = _placeColorFixpoints[placeID];
            std::cout << "Place: " << place.name << " in queue: " << placeColorFixpoint.inQueue  << " with colortype " << place.type->getName() << std::endl;
            
            //uint32_t index = 0;

            // for (auto color : *place.type) {
            //     std::cout << "Color " << color.toString() << " has index " << index << std::endl;
            //     index++;
            // }
            for(auto fixpointPair : placeColorFixpoint.constraints._intervals) {
                std::cout << "[";
                for(auto range : fixpointPair._ranges) {
                    std::cout << range._lower << "-" << range._upper << ", ";
                }
                std::cout << "]"<< std::endl;                    
            }

            std::cout << std::endl;
        }
        

    }

    void ColoredPetriNetBuilder::computePlaceColorFixpoint() {

        auto start = std::chrono::high_resolution_clock::now();

        while(!_placeFixpointQueue.empty()){
            uint32_t currentPlaceId = _placeFixpointQueue.back();
            _placeFixpointQueue.pop_back();
            _placeColorFixpoints[currentPlaceId].inQueue = false;

            std::cout << "Place " << _places[currentPlaceId].name << std::endl;
 
            std::vector<uint32_t> connectedTransitions = _placePostTransitionMap[currentPlaceId];

            for (uint32_t transitionId : connectedTransitions) {
                Colored::Transition& transition = _transitions[transitionId];
                if (transition.considered) break;
                bool transitionActivated = true;
                //maybe this can be avoided with a better implementation
                transition.variableMap.clear();
                std::cout << "Transition " << transition.name << std::endl;

                if(!_arcIntervals.count(transitionId)){
                    _arcIntervals[transitionId] = setupTransitionVars(transition);
                }

                // for(auto& arcInterval : _arcIntervals[transitionId]){
                //     arcInterval.second.resetIntervals();
                // } 
                           

                processInputArcs(transition, currentPlaceId, transitionId, transitionActivated);
                
                if (transitionActivated) {
                    processOutputArcs(transition);
                }              
            }
        }
        
        auto end = std::chrono::high_resolution_clock::now();
        _fixPointCreationTime = (std::chrono::duration_cast<std::chrono::microseconds>(end - start).count())*0.000001;
        printPlaceTable();
        //We should not need to keep colors in places after we have found fixpoint
        _placeColorFixpoints.clear();
    }

    std::unordered_map<uint32_t, Colored::ArcIntervals> ColoredPetriNetBuilder::setupTransitionVars(Colored::Transition transition){
        std::unordered_map<uint32_t, Colored::ArcIntervals> res;
        for(auto arc : transition.input_arcs){
            std::set<const Colored::Variable *> variables;
            std::unordered_map<uint32_t, const Colored::Variable *> varPositions;
            std::unordered_map<const Colored::Variable *, std::vector<std::pair<uint32_t, int32_t>>>  varModifiersMap;
            std::unordered_map<const Colored::Variable *, std::pair<uint32_t, int32_t>> varIndexModMap;
            arc.expr->getVariables(variables, varPositions, varModifiersMap);

            for(auto varModifierPair : varModifiersMap){
                int32_t varModifier = (*varModifierPair.second.begin()).second;

                uint32_t firstIndex = 0;
                for(auto pair : varPositions){
                    if (pair.second == varModifierPair.first){
                        firstIndex = pair.first;
                        break;
                    }
                }
                varIndexModMap[varModifierPair.first] = std::make_pair(firstIndex, varModifier);
            }

            Reachability::intervalTuple_t newRangeInterval;
            Colored::ArcIntervals newArcInterval(&_placeColorFixpoints[arc.place], varIndexModMap, newRangeInterval);
            res[arc.place] = newArcInterval;               
        }
        return res;
    }



    void ColoredPetriNetBuilder::processInputArcs(Colored::Transition& transition, uint32_t currentPlaceId, uint32_t transitionId, bool &transitionActivated) {
        for (auto arc : transition.input_arcs) {
            std::cout << "has arc "<< arc.expr.get()->toString() << std::endl;
            PetriEngine::Colored::ColorFixpoint& curCFP = _placeColorFixpoints[arc.place];
            //std::cout << "Cur place point " << std::endl;
            //curCFP.constraints.print();

            Colored::ArcIntervals& arcInterval = _arcIntervals[transitionId][arc.place];
            uint32_t index = 0;
            arcInterval._intervalTuple._intervals.clear();

            if(!arc.expr->getArcIntervals(arcInterval, curCFP, &index)){
                std::cout << "Failed to get arc intervals" << std::endl;
                transitionActivated = false;
                return;
            }
            for(auto& interval : arcInterval._intervalTuple._intervals){
                interval._active = true;
            }  
        }

        if(getVarIntervals(transition.variableMap, transitionId)){
            std::cout << transition.name << " var intervals" << std::endl;
            for (auto& pair : transition.variableMap){
                pair.second.mergeIntervals();
                std::cout << pair.first->name << std::endl;
                pair.second.print();
            }
            if(transition.guard != nullptr) {
                transition.guard->restrictVars(transition.variableMap);

                for(auto varPair : transition.variableMap){
                    //varPair.second.removeInactiveIntervals();
                    if(!varPair.second.hasValidIntervals()){
                        std::cout << "Could not find valid intervals for " << varPair.first->name << std::endl;
                        varPair.second.print();
                        transitionActivated = false; 
                        return;
                    }
                }
            }
        } else {
            std::cout << "getting var intervals failed " << std::endl;
            transitionActivated = false;
        }                                            
    }

    //could be expanded to handle when a variable apears multiple times on an arc with different modifiers
    bool ColoredPetriNetBuilder::getVarIntervals(std::unordered_map<const Colored::Variable *, Reachability::intervalTuple_t>& variableMap, uint32_t transitionId){
        bool stabilized = false;
        
        while(!stabilized){
            stabilized = true;
            for(auto& arcIntervals : _arcIntervals[transitionId]){
                for(auto pair : arcIntervals.second._varIndexModMap){
                    auto varPosition = pair.second.first;
                    auto varModifier = pair.second.second;
                    if(variableMap.count(pair.first) == 0){                  
                        Reachability::intervalTuple_t varIntervalTuple;
                        for(uint32_t i = 0; i < arcIntervals.second._intervalTuple._intervals.size(); i++){
                            auto interval = &arcIntervals.second._intervalTuple._intervals[i];
                            if(!interval->_active){
                                continue;
                            }
                            auto intervals = getIntervalsFromInterval(interval, varPosition, varModifier, pair.first); 
                                                
                            for(auto varInterval : intervals){
                                // std::cout << "Interval: ";
                                // varInterval.print();
                                // std::cout << std::endl;
                                varInterval._parentIntervals[arcIntervals.first].insert(interval);
                                varIntervalTuple.addInterval(varInterval);
                            }                        
                        }
                        varIntervalTuple.mergeIntervals();                  
                        variableMap[pair.first] = varIntervalTuple;
                    } else {    
                        std::vector<uint32_t> unusedIntervals; 
                        Reachability::intervalTuple_t collectedIntervalTuple;
                        for(uint32_t i = 0; i < arcIntervals.second._intervalTuple._intervals.size(); i++){
                            auto interval = &arcIntervals.second._intervalTuple._intervals[i];
                            if(!interval->_active){
                                continue;
                            }
                            bool intervalUsed = false;
                            Reachability::intervalTuple_t newIntervalTuple;
                            auto varIntervals = getIntervalsFromInterval(interval, varPosition, varModifier, pair.first);

                            for (auto arcVarInterval : varIntervals){
                                for (auto varInterval : variableMap[pair.first]._intervals){
                                    // std::cout << "Arc Interval: ";
                                    // arcVarInterval.print();
                                    // std::cout << std::endl;
                                    // std::cout << "Stored Interval: ";
                                    // varInterval.print();
                                    // std::cout << std::endl;
                                    auto overlappingInterval = arcVarInterval.getOverlap(varInterval);
                                    

                                    if(overlappingInterval.isSound()){
                                        // std::cout << "Found sound Interval: ";
                                        // overlappingInterval.print();
                                        // std::cout << std::endl;
                                        intervalUsed = true;
                                        overlappingInterval._parentIntervals = varInterval._parentIntervals;
                                        overlappingInterval._parentIntervals[arcIntervals.first].insert(interval);
                                        newIntervalTuple.addInterval(overlappingInterval);
                                    }
                                }
                            }
                            if(!intervalUsed){
                                stabilized = false;
                                unusedIntervals.push_back(i);
                            }
                            for(auto newInterval : newIntervalTuple._intervals){
                                collectedIntervalTuple.addInterval(newInterval);
                            }                            
                        }
                        // std::cout << "Collected intervals before are" << std::endl;
                        // collectedIntervalTuple.print();
                        collectedIntervalTuple.mergeIntervals();
                        // std::cout << "Collected intervals are" << std::endl;
                        // collectedIntervalTuple.print();
                        variableMap[pair.first] = collectedIntervalTuple;

                        for(auto unusedInterval : unusedIntervals){
                            arcIntervals.second._intervalTuple._intervals[unusedInterval]._active = false;
                        }                        
                    }
                    //If we do not find any valid intervals for an arc, then we can stop as there will not be any intervals
                    //which are valid for all arcs
                    if(!variableMap[pair.first].hasValidIntervals()){
                        std::cout << "Did not find valid intervals for " << pair.first->name << std::endl;
                        variableMap[pair.first].print();
                        return false;
                    }
                }
            }
        }
        return true;
    }

    std::vector<Reachability::interval_t> ColoredPetriNetBuilder::getIntervalsFromInterval(Reachability::interval_t *interval, uint32_t varPosition, int32_t varModifier, const Colored::Variable * var){
        std::vector<Reachability::interval_t> varIntervals;
        Reachability::interval_t firstVarInterval;
        varIntervals.push_back(firstVarInterval);
        for(uint32_t i = varPosition; i < varPosition + var->colorType->productSize(); i++){
            std::vector<Colored::ColorType*> varColorTypes;
            var->colorType->getColortypes(varColorTypes);
            auto ctSize = varColorTypes[i - varPosition]->size();
            uint32_t lower = (interval->operator[](i)._lower + varModifier) % ctSize;
            uint32_t upper = (interval->operator[](i)._upper + varModifier) % ctSize;

            if(lower > upper ){
                std::vector<Reachability::interval_t> newIntervals;
                for (auto& varInterval : varIntervals){
                    Reachability::interval_t newVarInterval = varInterval; 
                    newVarInterval._siblingIntervals.insert(&varInterval);
                    varInterval._siblingIntervals.insert(&newVarInterval);                                   
                    varInterval.addRange(0, upper);
                    newVarInterval.addRange(lower, ctSize -1);
                    newIntervals.push_back(newVarInterval);
                }

                varIntervals.insert(varIntervals.end(), newIntervals.begin(), newIntervals.end());
            } else {
                for (auto& varInterval : varIntervals){
                    varInterval.addRange(lower, upper);
                }
            }            
        }
        return varIntervals;
    }

    void ColoredPetriNetBuilder::processOutputArcs(Colored::Transition& transition) {
        bool transitionHasVarOutArcs = false;

        std::cout << transition.name << " activated" << std::endl;

        for (auto& arc : transition.output_arcs) {
            Colored::ColorFixpoint& placeFixpoint = _placeColorFixpoints[arc.place];

            //used to check if colors are added to the place. The total distance between upper and
            //lower bounds should grow when more colors are added and as we cannot remove colors this
            //can be checked by summing the differences
            uint32_t colorsBefore = 0;
            for (auto interval : placeFixpoint.constraints._intervals) {
                uint32_t intervalColors = 1;
                for(auto range: interval._ranges) {
                    intervalColors *= 1+  range._upper - range._lower;
                }  
                colorsBefore += intervalColors;              
            }
                
            std::set<const Colored::Variable *> variables;
            arc.expr->getVariables(variables);           

            if (!variables.empty()) {
                transitionHasVarOutArcs = true;
            }
            auto intervals = arc.expr->getOutputIntervals(transition.variableMap);

            for(auto interval : intervals._intervals){
                placeFixpoint.constraints.addInterval(interval);    
            }
            
            placeFixpoint.constraints.mergeIntervals();    

            if (!placeFixpoint.inQueue) {
                uint32_t colorsAfter = 0;
                for (auto interval : placeFixpoint.constraints._intervals) {
                    uint32_t intervalColors = 1;
                    for(auto range: interval._ranges) {
                        intervalColors *= 1+  range._upper - range._lower;
                    }  
                    colorsAfter += intervalColors;                        
                }
                if (colorsAfter > colorsBefore) {
                    _placeFixpointQueue.push_back(arc.place);
                    placeFixpoint.inQueue = true;
                }
            }                   
        }

        //If there are no variables among the out arcs of a transition 
        // and it has been activated, there is no reason to cosider it again
        if(!transitionHasVarOutArcs) {
            transition.considered = true;
        }
    }

    PetriNetBuilder& ColoredPetriNetBuilder::unfold() {
        if (_stripped) assert(false);
        if (_isColored && !_unfolded) {
            auto start = std::chrono::high_resolution_clock::now();
            //for (auto& place : _places) {
            //    unfoldPlace(place);
            //}

            std::cout << "Unfolding" << std::endl;

            for (auto& transition : _transitions) {
                unfoldTransition(transition);
            }
            for (auto& place : _places) {
               handleOrphanPlace(place);
            }

            _unfolded = true;
            auto end = std::chrono::high_resolution_clock::now();
            _time = (std::chrono::duration_cast<std::chrono::microseconds>(end - start).count())*0.000001;
        }

        return _ptBuilder;
    }
    //Due to the way we unfold places, we only unfold palces connected to an arc (which makes sense)
    //However, in queries asking about orphan places it cannot find these, as they have not been unfolded
    //so we make a placeholder place which just has tokens equal to the number of colored tokens
    //Ideally, orphan places should just be translated to a constant in the query
    void ColoredPetriNetBuilder::handleOrphanPlace(Colored::Place& place) {
        if(_ptplacenames.count(place.name) <= 0){
            std::string name = place.name + "_" + std::to_string(place.marking.size());
            _ptBuilder.addPlace(name, place.marking.size(), 0.0, 0.0);
            _ptplacenames[place.name][0] = std::move(name);
        }
        
        //++_nptplaces;
        
    }

    void ColoredPetriNetBuilder::unfoldPlace(Colored::Place& place) {
        // auto placeId = _placenames[place.name];
        // auto placeFixpoint = _placeColorFixpoints[placeId];
        // for (size_t i = placeFixpoint.interval_lower; i <= placeFixpoint.interval_upper; ++i) {
        //     std::string name = place.name + "_" + std::to_string(i);
        //     const Colored::Color* color = &place.type->operator[](i);
        //     _ptBuilder.addPlace(name, place.marking[color], 0.0, 0.0);
        //     _ptplacenames[place.name][color->getId()] = std::move(name);
        //     ++_nptplaces;
        // }
    }

    void ColoredPetriNetBuilder::unfoldTransition(Colored::Transition& transition) {
        
        BindingGenerator gen(transition, _colors);
        size_t i = 0;
        for (auto b : gen) {

            //Print all bindings
            // std::cout << transition.name << std::endl;
            // for (auto test : b){
            //     std::cout << "Binding '" << test.first << "\t" << *test.second << "' in bindingds." << std::endl;
            // }
            // std::cout << std::endl;
            
            
            std::string name = transition.name + "_" + std::to_string(i++);
            _ptBuilder.addTransition(name, 0.0, 0.0);
            _pttransitionnames[transition.name].push_back(name);
            ++_npttransitions;
            for (auto& arc : transition.input_arcs) {
                unfoldArc(arc, b, name, true );
            }
            for (auto& arc : transition.output_arcs) {
                unfoldArc(arc, b, name, false);
            }
        }
    }

    void ColoredPetriNetBuilder::unfoldArc(Colored::Arc& arc, Colored::ExpressionContext::BindingMap& binding, std::string& tName, bool input) {
        Colored::ExpressionContext context {binding, _colors};
        auto ms = arc.expr->eval(context);       

        for (const auto& color : ms) {
            if (color.second == 0) {
                continue;
            }
            const PetriEngine::Colored::Place& place = _places[arc.place];
            const std::string& pName = _ptplacenames[place.name][color.first->getId()];
            if (pName.empty()) {
                
                std::string name = place.name + "_" + std::to_string(color.first->getId());
                _ptBuilder.addPlace(name, place.marking[color.first], 0.0, 0.0);
                _ptplacenames[place.name][color.first->getId()] = std::move(name);
                ++_nptplaces;                
            }
            if (arc.input) {
                _ptBuilder.addInputArc(pName, tName, false, color.second);
            } else {
                _ptBuilder.addOutputArc(tName, pName, color.second);
            }
            ++_nptarcs;
        }
    }

    PetriNetBuilder& ColoredPetriNetBuilder::stripColors() {
        if (_unfolded) assert(false);
        if (_isColored && !_stripped) {
            for (auto& place : _places) {
                _ptBuilder.addPlace(place.name, place.marking.size(), 0.0, 0.0);
            }

            for (auto& transition : _transitions) {
                _ptBuilder.addTransition(transition.name, 0.0, 0.0);
                for (auto& arc : transition.input_arcs) {
                    try {
                        _ptBuilder.addInputArc(_places[arc.place].name, _transitions[arc.transition].name, false,
                                                arc.expr->weight());
                    } catch (Colored::WeightException& e) {
                        std::cerr << "Exception on input arc: " << arcToString(arc) << std::endl;
                        std::cerr << "In expression: " << arc.expr->toString() << std::endl;
                        std::cerr << e.what() << std::endl;
                        exit(ErrorCode);
                    }
                }
                for (auto& arc : transition.output_arcs) {
                    try {
                        _ptBuilder.addOutputArc(_transitions[arc.transition].name, _places[arc.place].name,
                                                arc.expr->weight());
                    } catch (Colored::WeightException& e) {
                        std::cerr << "Exception on output arc: " << arcToString(arc) << std::endl;
                        std::cerr << "In expression: " << arc.expr->toString() << std::endl;
                        std::cerr << e.what() << std::endl;
                        exit(ErrorCode);
                    }
                }
            }

            _stripped = true;
            _isColored = false;
        }

        return _ptBuilder;
    }

    std::string ColoredPetriNetBuilder::arcToString(Colored::Arc& arc) const {
        return !arc.input ? "(" + _transitions[arc.transition].name + ", " + _places[arc.place].name + ")" :
               "(" + _places[arc.place].name + ", " + _transitions[arc.transition].name + ")";
    }

    BindingGenerator::Iterator::Iterator(BindingGenerator* generator)
            : _generator(generator)
    {
    }

    bool BindingGenerator::Iterator::operator==(Iterator& other) {
        return _generator == other._generator;
    }

    bool BindingGenerator::Iterator::operator!=(Iterator& other) {
        return _generator != other._generator;
    }

    BindingGenerator::Iterator& BindingGenerator::Iterator::operator++() {
        _generator->nextBinding();
        if (_generator->_isDone) {
            _generator = nullptr;
        }
        return *this;
    }

    const Colored::ExpressionContext::BindingMap BindingGenerator::Iterator::operator++(int) {
        auto prev = _generator->currentBinding();
        ++*this;
        return prev;
    }

    Colored::ExpressionContext::BindingMap& BindingGenerator::Iterator::operator*() {
        return _generator->currentBinding();
    }
        BindingGenerator::BindingGenerator(Colored::Transition& transition,
            ColorTypeMap& colorTypes)
        : _colorTypes(colorTypes), _transition(transition)
    {
        _isDone = false;
        _noValidBindings = false;
        _expr = _transition.guard;
        std::set<const Colored::Variable*> variables;
        if (_expr != nullptr) {
            _expr->getVariables(variables);
        }
        for (auto arc : _transition.input_arcs) {
            assert(arc.expr != nullptr);
            arc.expr->getVariables(variables);
        }
        for (auto arc : _transition.output_arcs) {
            assert(arc.expr != nullptr);
            arc.expr->getVariables(variables);
        }
        std::cout << "Vars for " << _transition.name << " are bound to" << std::endl;
        for (auto& pair : _transition.variableMap){
            pair.second.mergeIntervals();
            std::cout << pair.first->name << std::endl;
            pair.second.print();
        }
        
        for (auto var : variables) {
            if(_transition.variableMap[var]._intervals.empty()){
                _noValidBindings = true;
                break;
            }
            auto color = var->colorType->getColor(_transition.variableMap[var].getLowerIds());
            _bindings[var] = color;
        }
        
        if (!_noValidBindings && !eval())
            nextBinding();
    }


    bool BindingGenerator::eval() {
        if (_expr == nullptr)
            return true;

        Colored::ExpressionContext context {_bindings, _colorTypes};
        return _expr->eval(context);
    }

    Colored::ExpressionContext::BindingMap& BindingGenerator::nextBinding() {
        bool test = false;
        while (!test) {
            
            for (auto& _binding : _bindings) {
                auto varInterval = _transition.variableMap[_binding.first];
                std::vector<uint32_t> colorIds;
                _binding.second->getTupleId(&colorIds);
                auto nextIntervalBinding = varInterval.isRangeEnd(colorIds);

                if (nextIntervalBinding.size() == 0){
                    _binding.second = &_binding.second->operator++();
                    break;                    
                } else {
                    _binding.second = _binding.second->getColorType()->getColor(nextIntervalBinding.getLowerIds());
                }
            }
            
            if (isInitial()) {
                _isDone = true;
                break;
            }      
            test = eval();
            /*if(_transition.name == "Start"){
                for (auto& _binding : _bindings){
                    cout << "color " << _binding.second->getColorName() << " for " << _binding.first << " is " << test << endl;
                }                
            }*/         
        }
        
        return _bindings;
    }

    Colored::ExpressionContext::BindingMap& BindingGenerator::currentBinding() {
        return _bindings;
    }

    bool BindingGenerator::isInitial() const {
        for (auto& b : _bindings) {
            std::vector<uint32_t> colorIds;
            b.second->getTupleId(&colorIds);
            if (colorIds != _transition.variableMap[b.first].getLowerIds()) return false;
        }
        return true;
    }

    // bool BindingGenerator::isFinal() const {
    //     for (auto& b : _bindings) {
    //         if (b.second->getId() != _transition.variableIntervals[b.first].getLower()) {
    //             return false;
    //         }
    //     }
    //     return true;
    // }

    BindingGenerator::Iterator BindingGenerator::begin() {
        if(_noValidBindings){
            return {nullptr};
        }
        return {this};
    }

    BindingGenerator::Iterator BindingGenerator::end() {
        return {nullptr};
    }

}

