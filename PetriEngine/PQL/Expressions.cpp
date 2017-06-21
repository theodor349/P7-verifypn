/* PeTe - Petri Engine exTremE
 * Copyright (C) 2011  Jonas Finnemann Jensen <jopsen@gmail.com>,
 *                     Thomas Søndersø Nielsen <primogens@gmail.com>,
 *                     Lars Kærlund Østergaard <larsko@gmail.com>,
 *                     Peter Gjøl Jensen <root@petergjoel.dk>
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
#include "Contexts.h"
#include "Expressions.h"

#include <sstream>
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <iostream>
#include <set>
#include <cmath>

using namespace PetriEngine::Simplification;

namespace PetriEngine {
    namespace PQL {
        
        std::ostream& generateTabs(std::ostream& out, uint32_t tabs) {

            for(uint32_t i = 0; i < tabs; i++) {
                out << "  ";
            }
            return out;
        }
        
        // CONSTANTS
        Condition_ptr BooleanCondition::FALSE_CONDITION = std::make_shared<BooleanCondition>(false);
        Condition_ptr BooleanCondition::TRUE_CONDITION = std::make_shared<BooleanCondition>(true);
        Condition_ptr DeadlockCondition::DEADLOCK = std::make_shared<DeadlockCondition>();
        
        
        Condition_ptr BooleanCondition::getShared(bool val)
        {
            if(val)
            {
                return TRUE_CONDITION;
            }
            else
            {
                return FALSE_CONDITION;
            }
        }
        
        /******************** To String ********************/

        void LiteralExpr::toString(std::ostream& out) const {
            out << _value;
        }

        void IdentifierExpr::toString(std::ostream& out) const {
            out << _name;
        }

        void NaryExpr::toString(std::ostream& ss) const {
            ss << "(";
            _exprs[0]->toString(ss);
            for(size_t i = 1; i < _exprs.size(); ++i)
            {
                ss << " " << op() << " ";
                _exprs[i]->toString(ss);
            }
            ss << ")";
        }

        void MinusExpr::toString(std::ostream& out) const {
            out << "-";
            _expr->toString(out);
        }

        void QuantifierCondition::toString(std::ostream& out) const {
            out << op() << " ";
            _cond->toString(out);
        }
        
        void UntilCondition::toString(std::ostream& out) const {
            out << op() << " (";
            _cond1->toString(out);
            out << " U ";
            _cond2->toString(out);
            out << ")";
        }
        
        void LogicalCondition::toString(std::ostream& out) const {
            out << "(";
            _cond1->toString(out);
            out << " " << op() << " ";
            _cond2->toString(out);
            out << ")";
        }

        void CompareCondition::toString(std::ostream& out) const {
            out << "(";
            _expr1->toString(out);
            out << " " << op() << " ";
            _expr2->toString(out);
            out <<")";
        }

        void NotCondition::toString(std::ostream& out) const {
            out << "(not ";
            _cond->toString(out);
            out << ")";
        }

        void BooleanCondition::toString(std::ostream& out) const {
            if (_value)
                out << "true";
            else
                out << "false";
        }

        void DeadlockCondition::toString(std::ostream& out) const {
            out << "deadlock";
        }

        /******************** To TAPAAL Query ********************/

        void QuantifierCondition::toTAPAALQuery(std::ostream& out,TAPAALConditionExportContext& context) const {
            out << op() << " ";
            _cond->toTAPAALQuery(out,context);
        }
        
        void UntilCondition::toTAPAALQuery(std::ostream& out,TAPAALConditionExportContext& context) const {
            out << op() << " (";
            _cond1->toTAPAALQuery(out, context);
            out << " U ";
            _cond2->toTAPAALQuery(out,context);
            out << ")";
        }
        
        void LogicalCondition::toTAPAALQuery(std::ostream& out,TAPAALConditionExportContext& context) const {
            out << " ( ";
            _cond1->toTAPAALQuery(out, context);
            out << " " << op() << " ";
            _cond2->toTAPAALQuery(out,context);
            out << " ) ";
        }

        void CompareCondition::toTAPAALQuery(std::ostream& out,TAPAALConditionExportContext& context) const {
            //If <id> <op> <literal>
            if (_expr1->type() == Expr::IdentifierExpr && _expr2->type() == Expr::LiteralExpr) {
                out << " ( " << context.netName << ".";
                _expr1->toString(out);
                out << " " << opTAPAAL() << " ";
                _expr2->toString(out);
                out << " ) ";
                //If <literal> <op> <id>
            } else if (_expr2->type() == Expr::IdentifierExpr && _expr1->type() == Expr::LiteralExpr) {
                out << " ( ";
                _expr1->toString(out);
                out << " " << sopTAPAAL() << " " << context.netName << ".";
                _expr2->toString(out);
                out << " ) ";
            } else {
                context.failed = true;
                out << " false ";
            }
        }

        void NotEqualCondition::toTAPAALQuery(std::ostream& out,TAPAALConditionExportContext& context) const {
            out << " !( ";
            CompareCondition::toTAPAALQuery(out,context);
            out << " ) ";
        }

        void NotCondition::toTAPAALQuery(std::ostream& out,TAPAALConditionExportContext& context) const {
            out << " !( ";
            _cond->toTAPAALQuery(out,context);
            out << " ) ";
        }

        void BooleanCondition::toTAPAALQuery(std::ostream& out,TAPAALConditionExportContext&) const {
            if (_value)
                out << "true";
            else
                out << "false";
        }

        void DeadlockCondition::toTAPAALQuery(std::ostream& out,TAPAALConditionExportContext&) const {
            out << "deadlock";
        }

        /******************** opTAPAAL ********************/

        std::string EqualCondition::opTAPAAL() const {
            return "=";
        }

        std::string NotEqualCondition::opTAPAAL() const {
            return "=";
        } //Handled with hack in NotEqualCondition::toTAPAALQuery

        std::string LessThanCondition::opTAPAAL() const {
            return "<";
        }

        std::string LessThanOrEqualCondition::opTAPAAL() const {
            return "<=";
        }

        std::string GreaterThanCondition::opTAPAAL() const {
            return ">";
        }

        std::string GreaterThanOrEqualCondition::opTAPAAL() const {
            return ">=";
        }

        std::string EqualCondition::sopTAPAAL() const {
            return "=";
        }

        std::string NotEqualCondition::sopTAPAAL() const {
            return "=";
        } //Handled with hack in NotEqualCondition::toTAPAALQuery

        std::string LessThanCondition::sopTAPAAL() const {
            return ">=";
        }

        std::string LessThanOrEqualCondition::sopTAPAAL() const {
            return ">";
        }

        std::string GreaterThanCondition::sopTAPAAL() const {
            return "<=";
        }

        std::string GreaterThanOrEqualCondition::sopTAPAAL() const {
            return "<";
        }

        /******************** Context Analysis ********************/

        void NaryExpr::analyze(AnalysisContext& context) {
            for(auto& e : _exprs) e->analyze(context);
        }

        void MinusExpr::analyze(AnalysisContext& context) {
            _expr->analyze(context);
        }

        void LiteralExpr::analyze(AnalysisContext&) {
            return;
        }

        void IdentifierExpr::analyze(AnalysisContext& context) {
            AnalysisContext::ResolutionResult result = context.resolve(_name);
            if (result.success) {
                _offsetInMarking = result.offset;
            } else {
                ExprError error("Unable to resolve identifier \"" + _name + "\"",
                        _name.length());
                context.reportError(error);
            }
        }

        void QuantifierCondition::analyze(AnalysisContext& context) {
            _cond->analyze(context);
        }
        
        void UntilCondition::analyze(AnalysisContext& context) {
            _cond1->analyze(context);
            _cond2->analyze(context);
        }
        
        void LogicalCondition::analyze(AnalysisContext& context) {
            _cond1->analyze(context);
            _cond2->analyze(context);
        }

        void CompareCondition::analyze(AnalysisContext& context) {
            _expr1->analyze(context);
            _expr2->analyze(context);
        }

        void NotCondition::analyze(AnalysisContext& context) {
            _cond->analyze(context);
        }

        void BooleanCondition::analyze(AnalysisContext&) {
        }

        void DeadlockCondition::analyze(AnalysisContext& c) {
            c.setHasDeadlock();
        }

        /******************** Evaluation ********************/

        int NaryExpr::evaluate(const EvaluationContext& context) const {
            int r = _exprs[0]->evaluate(context);
            for(size_t i = 1; i < _exprs.size(); ++i)
            {
                r = apply(r, _exprs[i]->evaluate(context));
            }
            return r;
        }

        int MinusExpr::evaluate(const EvaluationContext& context) const {
            return -(_expr->evaluate(context));
        }

        int LiteralExpr::evaluate(const EvaluationContext&) const {
            return _value;
        }

        int IdentifierExpr::evaluate(const EvaluationContext& context) const {
            assert(_offsetInMarking != -1);
            return context.marking()[_offsetInMarking];
        }

        bool QuantifierCondition::evaluate(const EvaluationContext& context) const {
            // Not implemented
	    assert(false);
	    return false;
        }
        
        bool UntilCondition::evaluate(const EvaluationContext& context) const {
            // Not implemented
            assert(false);
            return false;
        }
        
        bool LogicalCondition::evaluate(const EvaluationContext& context) const {
            bool b1 = _cond1->evaluate(context);
            bool b2 = _cond2->evaluate(context);
            return apply(b1, b2);
        }

        bool CompareCondition::evaluate(const EvaluationContext& context) const {
            int v1 = _expr1->evaluate(context);
            int v2 = _expr2->evaluate(context);
            return apply(v1, v2);
        }

        bool NotCondition::evaluate(const EvaluationContext& context) const {
            return !(_cond->evaluate(context));
        }

        bool BooleanCondition::evaluate(const EvaluationContext&) const {
            return _value;
        }

        bool DeadlockCondition::evaluate(const EvaluationContext& context) const {
            if (!context.net())
                return false;
            if (!context.net()->deadlocked(context.marking())) {
                return false;
            }
            return true;
        }
        
        /******************** Evaluation - save result ********************/
        bool QuantifierCondition::evalAndSet(const EvaluationContext& context) {
            // Not implemented
            assert(false);
	    return false;
        }
        
        bool UntilCondition::evalAndSet(const EvaluationContext& context) {
            // Not implemented
	    assert(false);
            return false;
        }        

        int NaryExpr::evalAndSet(const EvaluationContext& context) {
            int r = _exprs[0]->evalAndSet(context);
            for(size_t i = 1; i < _exprs.size(); ++i)
            {
                r = apply(r, _exprs[i]->evalAndSet(context));
            }
            setEval(r);
            return r;
        }

        int MinusExpr::evalAndSet(const EvaluationContext& context) {
            int res = -(_expr->evalAndSet(context));
            setEval(res);
            return res;
        }

        int LiteralExpr::evalAndSet(const EvaluationContext&) {
            setEval(_value);
            return _value;
        }

        int IdentifierExpr::evalAndSet(const EvaluationContext& context) {
            assert(_offsetInMarking != -1);
            int res = context.marking()[_offsetInMarking];
            setEval(res);
            return res;
        }

        bool LogicalCondition::evalAndSet(const EvaluationContext& context) {
            bool b1 = _cond1->evalAndSet(context);
            bool b2 = _cond2->evalAndSet(context);
            bool res = apply(b1, b2);
            setSatisfied(res);
            return res;
        }

        bool CompareCondition::evalAndSet(const EvaluationContext& context) {
            int v1 = _expr1->evalAndSet(context);
            int v2 = _expr2->evalAndSet(context);
            bool res = apply(v1, v2);
            setSatisfied(res);
            return res;
        }

        bool NotCondition::evalAndSet(const EvaluationContext& context) {
            bool res = !(_cond->evalAndSet(context));
            setSatisfied(res);
            return res;
        }

        bool BooleanCondition::evalAndSet(const EvaluationContext&) {
            setSatisfied(_value);
            return _value;
        }

        bool DeadlockCondition::evalAndSet(const EvaluationContext& context) {
            if (!context.net())
                return false;
            setSatisfied(context.net()->deadlocked(context.marking()));
            return isSatisfied();
        }
        
        /******************** Apply (BinaryExpr subclasses) ********************/

        int PlusExpr::apply(int v1, int v2) const {
            return v1 + v2;
        }

        int SubtractExpr::apply(int v1, int v2) const {
            return v1 - v2;
        }

        int MultiplyExpr::apply(int v1, int v2) const {
            return v1 * v2;
        }
        
        /******************** Apply (LogicalCondition subclasses) ********************/

        bool AndCondition::apply(bool b1, bool b2) const {
            return b1 && b2;
        }

        bool OrCondition::apply(bool b1, bool b2) const {
            return b1 || b2;
        }

        /******************** Apply (CompareCondition subclasses) ********************/

        bool EqualCondition::apply(int v1, int v2) const {
            return v1 == v2;
        }

        bool NotEqualCondition::apply(int v1, int v2) const {
            return v1 != v2;
        }

        bool LessThanCondition::apply(int v1, int v2) const {
            return v1 < v2;
        }

        bool LessThanOrEqualCondition::apply(int v1, int v2) const {
            return v1 <= v2;
        }

        bool GreaterThanCondition::apply(int v1, int v2) const {
            return v1 > v2;
        }

        bool GreaterThanOrEqualCondition::apply(int v1, int v2) const {
            return v1 >= v2;
        }

        /******************** Op (BinaryExpr subclasses) ********************/

        std::string PlusExpr::op() const {
            return "+";
        }

        std::string SubtractExpr::op() const {
            return "-";
        }

        std::string MultiplyExpr::op() const {
            return "*";
        }
        
        /******************** Op (QuantifierCondition subclasses) ********************/
        
        std::string EXCondition::op() const {
            return "EX";
        }
        
        std::string EGCondition::op() const {
            return "EG";
        }
        
        std::string EFCondition::op() const {
            return "EF";
        }
        
        std::string AXCondition::op() const {
            return "AX";
        }
        
        std::string AGCondition::op() const {
            return "AG";
        }
        
        std::string AFCondition::op() const {
            return "AF";
        }
        
        /******************** Op (UntilCondition subclasses) ********************/

        std::string EUCondition::op() const {
            return "E";
        }
        
        std::string AUCondition::op() const {
            return "A";
        }
        
        /******************** Op (LogicalCondition subclasses) ********************/

        std::string AndCondition::op() const {
            return "and";
        }

        std::string OrCondition::op() const {
            return "or";
        }

        /******************** Op (CompareCondition subclasses) ********************/

        std::string EqualCondition::op() const {
            return "==";
        }

        std::string NotEqualCondition::op() const {
            return "!=";
        }

        std::string LessThanCondition::op() const {
            return "<";
        }

        std::string LessThanOrEqualCondition::op() const {
            return "<=";
        }

        std::string GreaterThanCondition::op() const {
            return ">";
        }

        std::string GreaterThanOrEqualCondition::op() const {
            return ">=";
        }

        /******************** p-free Expression ********************/

        bool NaryExpr::pfree() const {
            for(auto& e : _exprs)
            {
                if(!e->pfree()) return false;
            }
            return true;
        }

        bool MinusExpr::pfree() const {
            return _expr->pfree();
        }

        bool LiteralExpr::pfree() const {
            return true;
        }

        bool IdentifierExpr::pfree() const {
            return false;
        }

        /******************** Expr::type() implementation ********************/

        Expr::Types PlusExpr::type() const {
            return Expr::PlusExpr;
        }

        Expr::Types SubtractExpr::type() const {
            return Expr::SubtractExpr;
        }

        Expr::Types MultiplyExpr::type() const {
            return Expr::MinusExpr;
        }

        Expr::Types MinusExpr::type() const {
            return Expr::MinusExpr;
        }

        Expr::Types LiteralExpr::type() const {
            return Expr::LiteralExpr;
        }

        Expr::Types IdentifierExpr::type() const {
            return Expr::IdentifierExpr;
        }

        /******************** Distance Condition ********************/

#define MAX(v1, v2)  (v1 > v2 ? v1 : v2)
#define MIN(v1, v2)  (v1 < v2 ? v1 : v2)

        uint32_t NotCondition::distance(DistanceContext& context) const {
            context.negate();
            uint32_t retval = _cond->distance(context);
            context.negate();
            return retval;
        }

        uint32_t BooleanCondition::distance(DistanceContext& context) const {
            if (context.negated() != _value)
                return 0;
            return std::numeric_limits<uint32_t>::max();
        }

        uint32_t DeadlockCondition::distance(DistanceContext& context) const {
            return 0;
        }
        
        uint32_t QuantifierCondition::distance(DistanceContext& context) const {
            // Not implemented
	    assert(false);
	    return 0;
        }
        
        uint32_t UntilCondition::distance(DistanceContext& context) const {
            // Not implemented
            assert(false);
	    return 0;
        }
        
        uint32_t LogicalCondition::distance(DistanceContext& context) const {
            uint32_t d1 = _cond1->distance(context);
            uint32_t d2 = _cond2->distance(context);
            return delta(d1, d2, context);
        }

        uint32_t AndCondition::delta(uint32_t d1,
                uint32_t d2,
                const DistanceContext& context) const {
                return d1 + d2;
        }

        uint32_t OrCondition::delta(uint32_t d1,
                uint32_t d2,
                const DistanceContext& context) const {
            if (context.negated())
                return MAX(d1, d2);
            else
                return MIN(d1, d2);
        }

        struct S {
            int d;
            unsigned int p;
        };

        uint32_t CompareCondition::distance(DistanceContext& context) const {
            int v1 = _expr1->evaluate(context);
            int v2 = _expr2->evaluate(context);
            return delta(v1, v2, context.negated());
        }

        uint32_t EqualCondition::delta(int v1, int v2, bool negated) const {
            if (!negated)
                return v1 - v2;
            else
                return v1 == v2 ? 1 : 0;
        }

        uint32_t NotEqualCondition::delta(int v1, int v2, bool negated) const {
            if (negated)
                return v1 - v2;
            else
                return v1 == v2 ? 1 : 0;
        }

        uint32_t LessThanCondition::delta(int v1, int v2, bool negated) const {
            if (!negated)
                return v1 < v2 ? 0 : v1 - v2 + 1;
            else
                return v1 >= v2 ? 0 : v2 - v1;
        }

        uint32_t LessThanOrEqualCondition::delta(int v1, int v2, bool negated) const {
            if (!negated)
                return v1 <= v2 ? 0 : v1 - v2;
            else
                return v1 > v2 ? 0 : v2 - v1 + 1;
        }

        uint32_t GreaterThanCondition::delta(int v1, int v2, bool negated) const {
            if (!negated)
                return v1 > v2 ? 0 : v2 - v1 + 1;
            else
                return v1 <= v2 ? 0 : v1 - v2;
        }

        uint32_t GreaterThanOrEqualCondition::delta(int v1, int v2, bool negated) const {
            if (!negated)
                return v1 >= v2 ? 0 : v2 - v1;
            else
                return v1 < v2 ? 0 : v1 - v2 + 1;
        }
        
        /******************** CTL Output ********************/ 
        
        void LiteralExpr::toXML(std::ostream& out,uint32_t tabs, bool tokencount) const {
            generateTabs(out,tabs) << "<integer-constant>" + std::to_string(_value) + "</integer-constant>\n";
        }
        
        void IdentifierExpr::toXML(std::ostream& out,uint32_t tabs, bool tokencount) const {
            if (tokencount) {
                generateTabs(out,tabs) << "<place>" << _name << "</place>\n";
            }
            else
            {
                generateTabs(out,tabs) << "<tokens-count>\n"; 
                generateTabs(out,tabs+1) << "<place>" << _name << "</place>\n";
                generateTabs(out,tabs) << "</tokens-count>\n";
            }
        }
        
        void PlusExpr::toXML(std::ostream& ss,uint32_t tabs, bool tokencount) const {
            if (tokencount) {
                for(auto& e : _exprs) e->toXML(ss,tabs, tokencount);
                return;
            }
            
            if(tk) {
                generateTabs(ss,tabs) << "<tokens-count>\n";
                for(auto& e : _exprs) e->toXML(ss,tabs+1, true);
                generateTabs(ss,tabs) << "</tokens-count>\n";
                return;
            }
            generateTabs(ss,tabs) << "<integer-sum>\n";
            for(auto& e : _exprs) e->toXML(ss,tabs+1, tokencount);
            generateTabs(ss,tabs) << "</integer-sum>\n";
        }
        
        void SubtractExpr::toXML(std::ostream& ss,uint32_t tabs, bool tokencount) const {
            generateTabs(ss,tabs) << "<integer-difference>\n";
            for(auto& e : _exprs) e->toXML(ss,tabs+1);
            generateTabs(ss,tabs) << "</integer-difference>\n";
        }
        
        void MultiplyExpr::toXML(std::ostream& ss,uint32_t tabs, bool tokencount) const {
            generateTabs(ss,tabs) << "<integer-product>\n";
            for(auto& e : _exprs) e->toXML(ss,tabs+1);
            generateTabs(ss,tabs) << "</integer-product>\n";
        }
        
        void MinusExpr::toXML(std::ostream& out,uint32_t tabs, bool tokencount) const {
            
            generateTabs(out,tabs) << "<integer-product>\n";
            _expr->toXML(out,tabs+1);
            generateTabs(out,tabs+1) << "<integer-difference>\n" ; generateTabs(out,tabs+2) <<
                    "<integer-constant>0</integer-constant>\n" ; generateTabs(out,tabs+2) << 
                    "<integer-constant>1</integer-constant>\n" ; generateTabs(out,tabs+1) <<
                    "</integer-difference>\n" ; generateTabs(out,tabs) << "</integer-product>\n";
        }
        
        void EXCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<exists-path>\n" ; generateTabs(out,tabs+1) << "<next>\n";
            _cond->toXML(out,tabs+2);
            generateTabs(out,tabs+1) << "</next>\n" ; generateTabs(out,tabs) << "</exists-path>\n";
        }

        void AXCondition::toXML(std::ostream& out,uint32_t tabs) const {           
            generateTabs(out,tabs) << "<all-paths>\n"; generateTabs(out,tabs+1) << "<next>\n";
            _cond->toXML(out,tabs+2);            
            generateTabs(out,tabs+1) << "</next>\n"; generateTabs(out,tabs) << "</all-paths>\n";
        }
        
        void EFCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<exist-path>\n" ; generateTabs(out,tabs+1) << "<finally>\n";
            _cond->toXML(out,tabs+2);
            generateTabs(out,tabs+1) << "</finally>\n" ; generateTabs(out,tabs) << "</exist-path>\n";
        }
        
        void AFCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<all-paths>\n" ; generateTabs(out,tabs+1) << "<finally>\n";
            _cond->toXML(out,tabs+2);
            generateTabs(out,tabs+1) << "</finally>\n" ; generateTabs(out,tabs) << "</all-paths>\n";
        }
        
        void EGCondition::toXML(std::ostream& out,uint32_t tabs) const {            
            generateTabs(out,tabs) << "<exist-path>\n" ; generateTabs(out,tabs+1) << "<globally>\n";
            _cond->toXML(out,tabs+2);            
            generateTabs(out,tabs+1) <<  "</globally>\n" ; generateTabs(out,tabs) << "</exist-path>\n";
        }
        
        void AGCondition::toXML(std::ostream& out,uint32_t tabs) const {            
            generateTabs(out,tabs) << "<all-paths>\n" ; generateTabs(out,tabs+1) << "<globally>\n";
            _cond->toXML(out,tabs+2);
            generateTabs(out,tabs+1) << "</globally>\n" ; generateTabs(out,tabs) << "</all-paths>\n";
        }
        
        void EUCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<exist-path>\n" ; generateTabs(out,tabs+1) << "<until>\n" ; generateTabs(out,tabs+2) << "<before>\n";
            _cond1->toXML(out,tabs+3);
            generateTabs(out,tabs+2) << "</before>\n" ; generateTabs(out,tabs+2) << "<reach>\n";
            _cond2->toXML(out,tabs+3);
            generateTabs(out,tabs+2) << "</reach>\n" ; generateTabs(out,tabs+1) << "</until>\n" ; generateTabs(out,tabs) << "</exist-path>\n";
        }
        
        void AUCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<all-paths>\n" ; generateTabs(out,tabs+1) << "<until>\n" ; generateTabs(out,tabs+2) << "<before>\n";
            _cond1->toXML(out,tabs+3);
            generateTabs(out,tabs+2) << "</before>\n" ; generateTabs(out,tabs+2) << "<reach>\n";
            _cond2->toXML(out,tabs+3);
            generateTabs(out,tabs+2) << "</reach>\n" ; generateTabs(out,tabs+1) << "</until>\n" ; generateTabs(out,tabs) << "</all-paths>\n";
        }
        
        void AndCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<conjunction>\n";
            _cond1->toXML(out,tabs+1);
            _cond2->toXML(out,tabs+1);
            generateTabs(out,tabs) << "</conjunction>\n";              
        }
        
        void OrCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<disjunction>\n";
            _cond1->toXML(out,tabs+1);
            _cond2->toXML(out,tabs+1);
            generateTabs(out,tabs) << "</disjunction>\n";              
        }
        
        void EqualCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<integer-eq>\n";
            _expr1->toXML(out,tabs+1);
            _expr2->toXML(out,tabs+1);
            generateTabs(out,tabs) << "</integer-eq>\n";  
        }
        
        void NotEqualCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<integer-ne>\n";
            _expr1->toXML(out,tabs+1);
            _expr2->toXML(out,tabs+1);
            generateTabs(out,tabs) << "</integer-ne>\n";  
        }
        
        void LessThanCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<integer-lt>\n";
            _expr1->toXML(out,tabs+1);
            _expr2->toXML(out,tabs+1);
            generateTabs(out,tabs) << "</integer-lt>\n";  
        }
        
        void LessThanOrEqualCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<integer-le>\n";
            _expr1->toXML(out,tabs+1);
            _expr2->toXML(out,tabs+1);
            generateTabs(out,tabs) << "</integer-le>\n";  
        }
        
        void GreaterThanCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<integer-gt>\n";
            _expr1->toXML(out,tabs+1);
            _expr2->toXML(out,tabs+1);
            generateTabs(out,tabs) << "</integer-gt>\n";  
        }
        
        void GreaterThanOrEqualCondition::toXML(std::ostream& out,uint32_t tabs) const {
            
            generateTabs(out,tabs) << "<integer-ge>\n";
            _expr1->toXML(out,tabs+1);
            _expr2->toXML(out,tabs+1);
            generateTabs(out,tabs) << "</integer-ge>\n";  
        }
        
        void NotCondition::toXML(std::ostream& out,uint32_t tabs) const {
            
            generateTabs(out,tabs) << "<negation>\n";
            _cond->toXML(out,tabs+1);
            generateTabs(out,tabs) << "</negation>\n";  
        }
        
        void BooleanCondition::toXML(std::ostream& out,uint32_t tabs) const {            
            generateTabs(out,tabs) << "<" << 
                    (_value ? "true" : "false") 
                    << "/>\n"; 
        }
        
        void DeadlockCondition::toXML(std::ostream& out,uint32_t tabs) const {
            generateTabs(out,tabs) << "<deadlock/>\n"; 
        }
        
        /******************** Query Simplification ********************/       
        
        Member LiteralExpr::constraint(SimplificationContext& context) const {
            return Member(_value);
        }
        
        Member IdentifierExpr::constraint(SimplificationContext& context) const {
            std::vector<int> row(context.net()->numberOfTransitions(), 0);
            row.shrink_to_fit();
            uint32_t p = offset();
            for (size_t t = 0; t < context.net()->numberOfTransitions(); t++) {
                row[t] = context.net()->outArc(t, p) - context.net()->inArc(p, t);
            }
            return Member(std::move(row), context.marking()[p]);
        }
        
        Member PlusExpr::constraint(SimplificationContext& context) const {
            Member res;
            for(auto& e : _exprs) res += e->constraint(context);
            return res;
        }
        
        Member SubtractExpr::constraint(SimplificationContext& context) const {
            Member res = _exprs[0]->constraint(context);
            for(size_t i = 1; i < _exprs.size(); ++i) res -= _exprs[i]->constraint(context);
            return res;
        }
        
        Member MultiplyExpr::constraint(SimplificationContext& context) const {
            Member res = _exprs[0]->constraint(context);
            for(size_t i = 1; i < _exprs.size(); ++i) res *= _exprs[i]->constraint(context);
            return res;
        }
        
        Member MinusExpr::constraint(SimplificationContext& context) const {
            Member neg(-1);
            return _expr->constraint(context) *= neg;
        }
        
        Retval simplifyEX(Retval& r, SimplificationContext& context) {
            if(r.formula->isTriviallyTrue() || !r.neglps->satisfiable(context, true)) {
                return Retval(std::make_shared<NotCondition>(
                        std::make_shared<DeadlockCondition>()));
            } else if(r.formula->isTriviallyFalse() || !r.lps->satisfiable(context, true)) {
                return Retval(BooleanCondition::FALSE_CONDITION);
            } else {
                return Retval(std::make_shared<EXCondition>(r.formula));
            }
        }
        
        Retval simplifyAX(Retval& r, SimplificationContext& context) {
            if(r.formula->isTriviallyTrue() || !r.neglps->satisfiable(context, true)){
                return Retval(BooleanCondition::TRUE_CONDITION);
            } else if(r.formula->isTriviallyFalse() || !r.lps->satisfiable(context, true)){
                return Retval(std::make_shared<DeadlockCondition>());
            } else{
                return Retval(std::make_shared<AXCondition>(r.formula));
            }
        }
        
        Retval simplifyEF(Retval& r, SimplificationContext& context){
            if(r.formula->isTriviallyTrue() || !r.neglps->satisfiable(context, true)){
                return Retval(BooleanCondition::TRUE_CONDITION);
            } else if(r.formula->isTriviallyFalse() || !r.lps->satisfiable(context, true)){
                return Retval(BooleanCondition::FALSE_CONDITION);
            } else {
                return Retval(std::make_shared<EFCondition>(r.formula));
            }
        }
        
        Retval simplifyAF(Retval& r, SimplificationContext& context){
            if(r.formula->isTriviallyTrue() || !r.neglps->satisfiable(context, true)){
                return Retval(BooleanCondition::TRUE_CONDITION);
            } else if(r.formula->isTriviallyFalse() || !r.lps->satisfiable(context, true)){
                return Retval(BooleanCondition::FALSE_CONDITION);
            } else {
                return Retval(std::make_shared<AFCondition>(r.formula));
            }
        }
        
        Retval simplifyEG(Retval& r, SimplificationContext& context){
            if(r.formula->isTriviallyTrue() || !r.neglps->satisfiable(context, true)){
                return Retval(BooleanCondition::TRUE_CONDITION);
            } else if(r.formula->isTriviallyFalse() || !r.lps->satisfiable(context, true)){
                return Retval(BooleanCondition::FALSE_CONDITION);
            } else {
                return Retval(std::make_shared<EGCondition>(r.formula));
            }
        }
        
        Retval simplifyAG(Retval& r, SimplificationContext& context){
            if(r.formula->isTriviallyTrue() || !r.neglps->satisfiable(context, true)){
                return Retval(BooleanCondition::TRUE_CONDITION);
            } else if(r.formula->isTriviallyFalse() || !r.lps->satisfiable(context, true)){
                return Retval(BooleanCondition::FALSE_CONDITION);
            } else {
                return Retval(std::make_shared<AGCondition>(r.formula));
            }
        }
        
        Retval EXCondition::simplify(SimplificationContext& context) const {
            Retval r = _cond->simplify(context);
            return context.negated() ? simplifyAX(r, context) : simplifyEX(r, context);
        }
        
        Retval AXCondition::simplify(SimplificationContext& context) const {
            Retval r = _cond->simplify(context);
            return context.negated() ? simplifyEX(r, context) : simplifyAX(r, context);
        }  
        
        Retval EFCondition::simplify(SimplificationContext& context) const {
            Retval r = _cond->simplify(context);
            return context.negated() ? simplifyAG(r, context) : simplifyEF(r, context);  
        }
        
        Retval AFCondition::simplify(SimplificationContext& context) const {
            Retval r = _cond->simplify(context);
            return context.negated() ? simplifyEG(r, context) : simplifyAF(r, context);  
        }
        
        Retval EGCondition::simplify(SimplificationContext& context) const {
            Retval r = _cond->simplify(context);
            return context.negated() ? simplifyAF(r, context) : simplifyEG(r, context);  
        }
        
        Retval AGCondition::simplify(SimplificationContext& context) const {
            Retval r = _cond->simplify(context);
            return context.negated() ? simplifyEF(r, context) : simplifyAG(r, context);  
        }
        
        Retval EUCondition::simplify(SimplificationContext& context) const {
            // cannot push negation any further
            bool neg = context.negated();
            context.setNegate(false);
            Retval r2 = _cond2->simplify(context);
            if(r2.formula->isTriviallyTrue() || !r2.neglps->satisfiable(context, true))
            {
                context.setNegate(neg);
                return neg ? 
                            Retval(BooleanCondition::FALSE_CONDITION) :
                            Retval(BooleanCondition::TRUE_CONDITION);
            }
            else if(r2.formula->isTriviallyFalse() || !r2.lps->satisfiable(context, true))
            {
                context.setNegate(neg);
                return neg ? 
                            Retval(BooleanCondition::TRUE_CONDITION) :
                            Retval(BooleanCondition::FALSE_CONDITION);                
            }
            Retval r1 = _cond1->simplify(context);
            context.setNegate(neg);
            
            if(context.negated()){
                if(r1.formula->isTriviallyTrue() || !r1.neglps->satisfiable(context, true)){
                    return Retval(std::make_shared<NotCondition>(
                            std::make_shared<EFCondition>(r2.formula)));
                } else if(r1.formula->isTriviallyFalse() || !r1.lps->satisfiable(context, true)){
                    return Retval(std::make_shared<NotCondition>(r2.formula));
                } else {
                    return Retval(std::make_shared<NotCondition>(
                            std::make_shared<EUCondition>(r1.formula, r2.formula)));
                }
            } else {
                if(r1.formula->isTriviallyTrue() || !r1.neglps->satisfiable(context, true)){
                    return Retval(std::make_shared<EFCondition>(r2.formula));
                } else if(r1.formula->isTriviallyFalse() || !r1.lps->satisfiable(context, true)){
                    return r2;
                } else {
                    return Retval(std::make_shared<EUCondition>(r1.formula, r2.formula));
                }
            }
        }
        
        Retval AUCondition::simplify(SimplificationContext& context) const {
            // cannot push negation any further
            bool neg = context.negated();
            context.setNegate(false);
            Retval r2 = _cond2->simplify(context);
            if(r2.formula->isTriviallyTrue() || !r2.neglps->satisfiable(context, true))
            {
                context.setNegate(neg);
                return neg ? 
                            Retval(BooleanCondition::FALSE_CONDITION) :
                            Retval(BooleanCondition::TRUE_CONDITION);
            }
            else if(r2.formula->isTriviallyFalse() || !r2.lps->satisfiable(context, true))
            {
                context.setNegate(neg);
                return neg ? 
                            Retval(BooleanCondition::TRUE_CONDITION) :
                            Retval(BooleanCondition::FALSE_CONDITION);                
            }
            Retval r1 = _cond1->simplify(context);
            context.setNegate(neg);
            
            if(context.negated()){
                if(r1.formula->isTriviallyTrue() || !r1.neglps->satisfiable(context, true)){
                    return Retval(std::make_shared<NotCondition>(
                            std::make_shared<AFCondition>(r2.formula)));
                } else if(r1.formula->isTriviallyFalse() || !r1.lps->satisfiable(context, true)){
                    return Retval(std::make_shared<NotCondition>(r2.formula));
                } else {
                    return Retval(std::make_shared<NotCondition>(
                            std::make_shared<AUCondition>(r1.formula, r2.formula)));
                }
            } else {
                if(r1.formula->isTriviallyTrue() || !r1.neglps->satisfiable(context, true)){
                    return Retval(std::make_shared<AFCondition>(r2.formula));
                } else if(r1.formula->isTriviallyFalse() || !r1.lps->satisfiable(context, true)){
                    return r2;
                } else {
                    return Retval(std::make_shared<AUCondition>(r1.formula, r2.formula));
                }
            }
        }
        
        Retval simplifyAnd(SimplificationContext& context, Retval&& r1, Retval&& r2) {
            try{
                if(r1.formula->isTriviallyFalse() || r2.formula->isTriviallyFalse()) {
                    return Retval(BooleanCondition::FALSE_CONDITION);
                } else if (r1.formula->isTriviallyTrue()) {
                    return std::move(r2);
                } else if (r2.formula->isTriviallyTrue()) {
                    return std::move(r1);
                }
                
                if(!context.timeout())
                {
                    r1.lps = std::make_shared<MergeCollection>(r1.lps, r2.lps);
                    if(!context.timeout() && !r1.lps->satisfiable(context)) {
                        return Retval(BooleanCondition::FALSE_CONDITION);
                    }
                    r1.neglps = std::make_shared<UnionCollection>(r1.neglps, r2.neglps);
                }
                else
                {
                    r1.lps->clear();
                    r1.neglps->clear();
                    r2.lps->clear();
                    r2.neglps->clear();
                }
                return Retval(std::make_shared<AndCondition>(r1.formula, r2.formula), std::move(r1.lps), std::move(r1.neglps)); 
            }
            catch(std::bad_alloc& e)
            {
                // we are out of memory, deal with it.
                std::cout<<"Query reduction: memory exceeded during LPS merge."<<std::endl;
                return Retval(std::make_shared<AndCondition>(r1.formula, r2.formula), 
                        std::move(r1.lps),
                        std::move(r1.neglps));
            }
        }
        
        Retval simplifyOr(SimplificationContext& context, Retval&& r1, Retval&& r2) {
            if(r1.formula->isTriviallyTrue() || r2.formula->isTriviallyTrue()) {
                return Retval(BooleanCondition::TRUE_CONDITION);
            } 
            
            if(r1.formula->isTriviallyFalse())
            {
                return std::move(r2);
            }
            else if(r2.formula->isTriviallyFalse())
            {
                return std::move(r1);
            }
            else if(!context.timeout())
            {
                r1.neglps = std::make_shared<MergeCollection>(r1.neglps, r2.neglps);
            }
            else
            {
                r1.lps->clear();
                r1.neglps->clear();
                r2.lps->clear();                
                r2.neglps->clear();
            }
            
            // Lets try to see if the r1 AND r2 can ever be false at the same time
            // If not, then we know that r1 || r2 must be true.
            // we check this by checking if !r1 && !r2 is unsat
            
            if(!context.timeout() && !r1.neglps->satisfiable(context))
            {
                return Retval(BooleanCondition::TRUE_CONDITION);
            }
            
            if (!context.timeout()){
                r1.lps = std::make_shared<UnionCollection>(r1.lps, r2.lps);
            }
            
            return Retval(std::make_shared<OrCondition>(r1.formula, r2.formula), std::move(r1.lps), std::move(r1.neglps));            
        }
        
        Retval AndCondition::simplify(SimplificationContext& context) const {
            if(context.timeout())
            {
                if(context.negated()) 
                    return Retval(std::make_shared<NotCondition>(
                            std::make_shared<AndCondition>(_cond1, _cond2)));
                else                  
                    return Retval(
                            std::make_shared<AndCondition>(_cond1, _cond2));
            }
            Retval r1, r2;
            bool succ1 = false, succ2 = false;
            try{
                r1 = _cond1->simplify(context);
                succ1 = true;
            }
            catch (std::bad_alloc& e) {};
            
            // negated becomes or -- so if r1 is trivially true,
            // or if not negated, and r1 is false -- we can short-circuit
            if(context.negated() && r1.formula->isTriviallyTrue())    
                return Retval(BooleanCondition::TRUE_CONDITION);
            else if(!context.negated() && r1.formula->isTriviallyFalse())    
                return Retval(BooleanCondition::FALSE_CONDITION);
            

            try{
                r2 = _cond2->simplify(context);
                succ2 = true;
            }
            catch (std::bad_alloc& e) {};
            if(!succ1 && !succ2) throw std::bad_alloc();
            else if(succ1 && !succ2) return r1;
            else if(succ2 && !succ1) return r2;
            else return context.negated()   ? simplifyOr(context, std::move(r1), std::move(r2)) 
                                            : simplifyAnd(context, std::move(r1), std::move(r2));
        }
        
        Retval OrCondition::simplify(SimplificationContext& context) const {            
            if(context.timeout())
            {
                if(context.negated()) 
                    return Retval(std::make_shared<NotCondition>(
                            std::make_shared<OrCondition>(_cond1, _cond2)));
                else                 
                    return Retval(std::make_shared<OrCondition>(_cond1, _cond2));
            }
            Retval r1 = _cond1->simplify(context);
            // negated becomes and -- so if r1 is trivially false,
            // or if not negated, and r1 is true -- we can short-circuit
            if(!context.negated() && r1.formula->isTriviallyTrue()) 
                return Retval(BooleanCondition::TRUE_CONDITION);
            else if(context.negated() && r1.formula->isTriviallyFalse()) 
                return Retval(BooleanCondition::FALSE_CONDITION);

            Retval r2 = _cond2->simplify(context);
            
            return context.negated() ?  simplifyAnd(context, std::move(r1), std::move(r2)) : 
                                        simplifyOr(context, std::move(r1), std::move(r2));
        }
        
        Retval EqualCondition::simplify(SimplificationContext& context) const {
            
            Member m1 = _expr1->constraint(context);
            Member m2 = _expr2->constraint(context);
            
            std::shared_ptr<AbstractProgramCollection> lps, neglps;
            if (!context.timeout() && m1.canAnalyze() && m2.canAnalyze()) {
                if ((m1.isZero() && m2.isZero()) || m1.substrationIsZero(m2)) {
                    return Retval(BooleanCondition::getShared(
                        context.negated() ? (m1.constant() != m2.constant()) : (m1.constant() == m2.constant())));
                } else {
                    int constant = m2.constant() - m1.constant();
                    m1 -= m2;
                    m2 = m1;
                    neglps = 
                            std::make_shared<MergeCollection>(
                            std::make_shared<SingleProgram>(context.cache(), std::move(m1), constant, Simplification::OP_GT),
                            std::make_shared<SingleProgram>(context.cache(), std::move(m2), constant, Simplification::OP_LT));
                    Member m3 = m2;
                    lps = std::make_shared<SingleProgram>(context.cache(), std::move(m3), constant, Simplification::OP_EQ);
                    
                    if(context.negated()) lps.swap(neglps);
                }
            } else {
                lps = std::make_shared<SingleProgram>();
            }
            
            if (!context.timeout() && !lps->satisfiable(context)) {
                return Retval(BooleanCondition::FALSE_CONDITION);
            } 
            else if(!context.timeout() && !neglps->satisfiable(context))
            {
                return Retval(BooleanCondition::TRUE_CONDITION);            
            } 
            else {
                if (context.negated()) {
                    return Retval(std::make_shared<NotEqualCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                } else {
                    return Retval(std::make_shared<EqualCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                }
            }
        }
        
        Retval NotEqualCondition::simplify(SimplificationContext& context) const {
            Member m1 = _expr1->constraint(context);
            Member m2 = _expr2->constraint(context);
            
            std::shared_ptr<AbstractProgramCollection> lps, neglps;

            if (!context.timeout() && m1.canAnalyze() && m2.canAnalyze()) {
                if ((m1.isZero() && m2.isZero()) || m1.substrationIsZero(m2)) {
                    return Retval(std::make_shared<BooleanCondition>(
                        context.negated() ? (m1.constant() == m2.constant()) : (m1.constant() != m2.constant())));
                } else{ 
                    int constant = m2.constant() - m1.constant();
                    m1 -= m2;
                    m2 = m1;
                    lps = 
                            std::make_shared<MergeCollection>(
                            std::make_shared<SingleProgram>(context.cache(), std::move(m1), constant, Simplification::OP_GT),
                            std::make_shared<SingleProgram>(context.cache(), std::move(m2), constant, Simplification::OP_LT));
                    Member m3 = m2;
                    neglps = std::make_shared<SingleProgram>(context.cache(), std::move(m3), constant, Simplification::OP_EQ); 
                    
                    if(context.negated()) lps.swap(neglps);
                }
            } else {
                lps = std::make_shared<SingleProgram>();
                neglps = std::make_shared<SingleProgram>();
            }
            
            if (!context.timeout() && !lps->satisfiable(context)) {
                return Retval(BooleanCondition::FALSE_CONDITION);
            } 
            else if(!context.timeout() && !neglps->satisfiable(context))
            {
                return Retval(BooleanCondition::TRUE_CONDITION);            
            }
            else {
                if (context.negated()) {
                    return Retval(std::make_shared<EqualCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                } else {
                    return Retval(std::make_shared<NotEqualCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                }                         
            }
        }
            
        Retval LessThanCondition::simplify(SimplificationContext& context) const {
            Member m1 = _expr1->constraint(context);
            Member m2 = _expr2->constraint(context);
            
            AbstractProgramCollection_ptr lps, neglps;
            if (!context.timeout() && m1.canAnalyze() && m2.canAnalyze()) {
                // test for trivial comparison
                Trivial eval = context.negated() ? m1 >= m2 : m1 < m2;
                if(eval != Trivial::Indeterminate)
                {
                    return Retval(BooleanCondition::getShared(eval == Trivial::True));
                }
                // if no trivial case
                else 
                {
                    int constant = m2.constant() - m1.constant();
                    m1 -= m2;
                    m2 = m1;
                    lps = std::make_shared<SingleProgram>(context.cache(), std::move(m1), constant, (context.negated() ? Simplification::OP_GE : Simplification::OP_LT));
                    neglps = std::make_shared<SingleProgram>(context.cache(), std::move(m2), constant, (!context.negated() ? Simplification::OP_GE : Simplification::OP_LT));
                }
            } else {
                lps = std::make_shared<SingleProgram>();
                neglps = std::make_shared<SingleProgram>();
            }
            
            if (!context.timeout() && !lps->satisfiable(context)) {
                return Retval(BooleanCondition::FALSE_CONDITION);
            }
            else if(!context.timeout() && !neglps->satisfiable(context))
            {
                return Retval(BooleanCondition::TRUE_CONDITION);                
            }
            else {
                if (context.negated()) {
                    return Retval(std::make_shared<GreaterThanOrEqualCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                } else {
                    return Retval(std::make_shared<LessThanCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                }                         
            }
        }        
        
        Retval LessThanOrEqualCondition::simplify(SimplificationContext& context) const {
            Member m1 = _expr1->constraint(context);
            Member m2 = _expr2->constraint(context);
            
            AbstractProgramCollection_ptr lps, neglps;
            if (!context.timeout() && m1.canAnalyze() && m2.canAnalyze()) {
                // test for trivial comparison
                Trivial eval = context.negated() ? m1 > m2 : m1 <= m2;
                if(eval != Trivial::Indeterminate) {
                    return Retval(BooleanCondition::getShared(eval == Trivial::True));
                } else { // if no trivial case
                    int constant = m2.constant() - m1.constant();
                    m1 -= m2;
                    m2 = m1;
                    lps = std::make_shared<SingleProgram>(context.cache(), std::move(m1), constant, (context.negated() ? Simplification::OP_GT : Simplification::OP_LE));
                    neglps = std::make_shared<SingleProgram>(context.cache(), std::move(m2), constant, (context.negated() ? Simplification::OP_LE : Simplification::OP_GT));
                }
            } else {
                lps = std::make_shared<SingleProgram>();
                neglps = std::make_shared<SingleProgram>();
            }

            if(!context.timeout() && !neglps->satisfiable(context)){
                return Retval(BooleanCondition::TRUE_CONDITION);
            } else if (!context.timeout() && !lps->satisfiable(context)) {
                return Retval(BooleanCondition::FALSE_CONDITION);
            } else {
                if (context.negated()) {
                    return Retval(std::make_shared<GreaterThanCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                } else {
                    return Retval(std::make_shared<LessThanOrEqualCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                }                         
            }
        }
        
        Retval GreaterThanCondition::simplify(SimplificationContext& context) const {
            Member m1 = _expr1->constraint(context);
            Member m2 = _expr2->constraint(context);
            
            AbstractProgramCollection_ptr lps, neglps;
            if (!context.timeout() && m1.canAnalyze() && m2.canAnalyze()) {
                // test for trivial comparison
                Trivial eval = context.negated() ? m1 <= m2 : m1 > m2;
                if(eval != Trivial::Indeterminate) {
                    return Retval(BooleanCondition::getShared(eval == Trivial::True));
                } else { // if no trivial case
                    int constant = m2.constant() - m1.constant();
                    m1 -= m2;
                    m2 = m1;
                    lps = std::make_shared<SingleProgram>(context.cache(), std::move(m1), constant, (context.negated() ? Simplification::OP_LE : Simplification::OP_GT));
                    neglps = std::make_shared<SingleProgram>(context.cache(), std::move(m2), constant, (context.negated() ? Simplification::OP_GT : Simplification::OP_LE));
                }
            } else {
                lps = std::make_shared<SingleProgram>();
                neglps = std::make_shared<SingleProgram>();
            }
            
            if(!context.timeout() && !neglps->satisfiable(context)) {
                return Retval(BooleanCondition::TRUE_CONDITION);
            }else if(!context.timeout() && !lps->satisfiable(context)) {
                return Retval(BooleanCondition::FALSE_CONDITION);
            } else {
                if (context.negated()) {
                    return Retval(std::make_shared<LessThanOrEqualCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                } else {
                    return Retval(std::make_shared<GreaterThanCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                }                         
            }
        }
        
        Retval GreaterThanOrEqualCondition::simplify(SimplificationContext& context) const {  
            Member m1 = _expr1->constraint(context);
            Member m2 = _expr2->constraint(context);
            
            AbstractProgramCollection_ptr lps, neglps;
            if (!context.timeout() && m1.canAnalyze() && m2.canAnalyze()) {
                // test for trivial comparison
                Trivial eval = context.negated() ? m1 < m2 : m1 >= m2;
                if(eval != Trivial::Indeterminate)
                {
                    return Retval(BooleanCondition::getShared(eval == Trivial::True));
                }
                // if no trivial case
                else 
                {
                    int constant = m2.constant() - m1.constant();
                    m1 -= m2;
                    m2 = m1;
                    lps = std::make_shared<SingleProgram>(context.cache(), std::move(m1), constant, (context.negated() ? Simplification::OP_LT : Simplification::OP_GE));
                    neglps = std::make_shared<SingleProgram>(context.cache(), std::move(m2), constant, (!context.negated() ? Simplification::OP_LT : Simplification::OP_GE));
                }
                
            } else {
                lps = std::make_shared<SingleProgram>();
                neglps = std::make_shared<SingleProgram>();
            }
            
            if (!context.timeout() && !lps->satisfiable(context)) 
            {
                return Retval(BooleanCondition::FALSE_CONDITION);
            } 
            else if(!context.timeout() && !neglps->satisfiable(context)) // EXPERIMENTAL
            {
                return Retval(BooleanCondition::TRUE_CONDITION);
            }
            else {
                if (context.negated()) {
                    return Retval(std::make_shared<LessThanCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                } else {
                    return Retval(std::make_shared<GreaterThanOrEqualCondition>(_expr1, _expr2), std::move(lps), std::move(neglps));
                }                         
            }
        }
        
        Retval NotCondition::simplify(SimplificationContext& context) const {
            context.negate();
            Retval r = _cond->simplify(context);
            context.negate();
            return r;
        }
        
        Retval BooleanCondition::simplify(SimplificationContext& context) const {
            if (context.negated()) {
                return Retval(getShared(!_value));
            } else {
                return Retval(getShared(_value));
            }
        }
        
        Retval DeadlockCondition::simplify(SimplificationContext& context) const {
            if (context.negated()) {
                return Retval(std::make_shared<NotCondition>(DeadlockCondition::DEADLOCK));
            } else {
                return Retval(DeadlockCondition::DEADLOCK);
            }
        }
        
        /******************** Check if query is a reachability query ********************/
        
        bool EXCondition::isReachability(uint32_t depth) const {
            return false;
        }
        
        bool EGCondition::isReachability(uint32_t depth) const {
            return false;
        }
        
        bool EFCondition::isReachability(uint32_t depth) const {
            return depth > 0 ? false : _cond->isReachability(depth + 1);
        }
        
        bool AXCondition::isReachability(uint32_t depth) const {
            return false;
        }
        
        bool AGCondition::isReachability(uint32_t depth) const {
            return depth > 0 ? false : _cond->isReachability(depth + 1);
        }
        
        bool AFCondition::isReachability(uint32_t depth) const {
            return false;
        }
        
        bool UntilCondition::isReachability(uint32_t depth) const {
            return false;
        }
        
        bool LogicalCondition::isReachability(uint32_t depth) const {
            return depth == 0 ? false : _cond1->isReachability(depth + 1) && _cond2->isReachability(depth + 1);
        }
        
        bool CompareCondition::isReachability(uint32_t depth) const {
            return depth > 0;
        }
        
        bool NotCondition::isReachability(uint32_t depth) const {
            return _cond->isReachability(depth);
        }
        
        bool BooleanCondition::isReachability(uint32_t depth) const {
            return depth > 0;
        }
        
        bool DeadlockCondition::isReachability(uint32_t depth) const {
            return depth > 0;
        }
        
        /******************** Check if query is an upper bound query ********************/
        
        bool QuantifierCondition::isUpperBound() {
            return _cond->isUpperBound();
        }
        
        bool UntilCondition::isUpperBound() {
            return false;
        }
        
        bool LogicalCondition::isUpperBound() {
            if (placeNameForBound().size() != 0) {
                return true;
            } else {
                return _cond1->isUpperBound() && _cond2->isUpperBound();
            }
        }
        
        bool CompareCondition::isUpperBound() {
            if (placeNameForBound().size() != 0) {
                return true;
            } else {
                return false;
            }
        }
        
        bool NotCondition::isUpperBound() {
            return false;
        }
        
        bool BooleanCondition::isUpperBound() {
            return false;
        }
        
        bool DeadlockCondition::isUpperBound() {
            return false;
        }
        
        
        /******************** Prepare Reachability Queries ********************/
        
        Condition_ptr EXCondition::prepareForReachability(bool negated) const {
            return NULL;
        }
        
        Condition_ptr EGCondition::prepareForReachability(bool negated) const {
            return NULL;
        }
        
        Condition_ptr EFCondition::prepareForReachability(bool negated) const {
            _cond->setInvariant(negated);
            return _cond;
        }
        
        Condition_ptr AXCondition::prepareForReachability(bool negated) const {
            return NULL;
        }
        
        Condition_ptr AGCondition::prepareForReachability(bool negated) const {
            Condition_ptr cond = std::make_shared<NotCondition>(_cond);
            cond->setInvariant(!negated);
            return cond;
        }
        
        Condition_ptr AFCondition::prepareForReachability(bool negated) const {
            return NULL;
        }
        
        Condition_ptr UntilCondition::prepareForReachability(bool negated) const {
            return NULL;
        }
        
        Condition_ptr LogicalCondition::prepareForReachability(bool negated) const {
            return NULL;
        }
        
        Condition_ptr CompareCondition::prepareForReachability(bool negated) const {
            return NULL;
        }
        
        Condition_ptr NotCondition::prepareForReachability(bool negated) const {
            return _cond->prepareForReachability(!negated);
        }
        
        Condition_ptr BooleanCondition::prepareForReachability(bool negated) const {
            return NULL;
        }
        
        Condition_ptr DeadlockCondition::prepareForReachability(bool negated) const {
            return NULL;
        }
        
        /******************** Stubborn reduction interesting transitions ********************/
        
        void PlusExpr::incr(ReducingSuccessorGenerator& generator) const { 
            for(auto& e : _exprs) e->incr(generator);                
        }
        
        void PlusExpr::decr(ReducingSuccessorGenerator& generator) const {
            for(auto& e : _exprs) e->decr(generator);                
        }
        
        void SubtractExpr::incr(ReducingSuccessorGenerator& generator) const {
            _exprs[0]->incr(generator);
            _exprs[1]->decr(generator);
        }
        
        void SubtractExpr::decr(ReducingSuccessorGenerator& generator) const {
            _exprs[0]->decr(generator);
            _exprs[1]->incr(generator);
        }
        
        void MultiplyExpr::incr(ReducingSuccessorGenerator& generator) const {
            for(auto& e : _exprs)
            {
                e->incr(generator);
                e->decr(generator);
            }
        }
        
        void MultiplyExpr::decr(ReducingSuccessorGenerator& generator) const {
            incr(generator);
        }
        
        void MinusExpr::incr(ReducingSuccessorGenerator& generator) const {
            // TODO not implemented
        }
        
        void MinusExpr::decr(ReducingSuccessorGenerator& generator) const {
            // TODO not implemented
        }

        void LiteralExpr::incr(ReducingSuccessorGenerator& generator) const {
            // Add nothing
        }
        
        void LiteralExpr::decr(ReducingSuccessorGenerator& generator) const {
            // Add nothing
        }

        void IdentifierExpr::incr(ReducingSuccessorGenerator& generator) const {
            generator.presetOf(_offsetInMarking);
        }
        
        void IdentifierExpr::decr(ReducingSuccessorGenerator& generator) const {
             generator.postsetOf(_offsetInMarking);
        }
        
        void QuantifierCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const{
            // Not implemented
        }
        
        void UntilCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const{
            // Not implemented
        }
        
        void AndCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            if(!negated){               // and
                if(!_cond2->isSatisfied()) { // TODO If both conditions are false, maybe use a heuristic to pick condition?
                    _cond2->findInteresting(generator, negated);
                } else {
                    _cond1->findInteresting(generator, negated);
                }
            } else {                    // or
                _cond1->findInteresting(generator, negated);
                _cond2->findInteresting(generator, negated);
            }
        }
        
        void OrCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            if(!negated){               // or
                _cond1->findInteresting(generator, negated);
                _cond2->findInteresting(generator, negated);
            } else {                    // and
                if(_cond2->isSatisfied()) {       
                    _cond2->findInteresting(generator, negated);
                } else {
                    _cond1->findInteresting(generator, negated);
                }
            }
        }
        
        void EqualCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            if(!negated){               // equal
                if(_expr1->getEval() == _expr2->getEval()) { return; }
                if(_expr1->getEval() > _expr2->getEval()){
                    _expr1->decr(generator);
                    _expr2->incr(generator);
                } else {
                    _expr1->incr(generator);
                    _expr2->decr(generator);
                }   
            } else {                    // not equal
                if(_expr1->getEval() != _expr2->getEval()) { return; }
                _expr1->incr(generator);
                _expr2->decr(generator);
                _expr1->incr(generator);
                _expr2->decr(generator);
            }
        }
        
        void NotEqualCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            if(!negated){               // not equal
                if(_expr1->getEval() != _expr2->getEval()) { return; }
                _expr1->incr(generator);
                _expr2->decr(generator);
                _expr1->incr(generator);
                _expr2->decr(generator);
            } else {                    // equal
                if(_expr1->getEval() == _expr2->getEval()) { return; }
                if(_expr1->getEval() > _expr2->getEval()){
                    _expr1->decr(generator);
                    _expr2->incr(generator);
                } else {
                    _expr1->incr(generator);
                    _expr2->decr(generator);
                }   
            }
        }
        
        void LessThanCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {                
            if(!negated){               // less than
                if(_expr1->getEval() < _expr2->getEval()) { return; }
                _expr1->decr(generator);
                _expr2->incr(generator);
            } else {                    // greater than or equal
                if(_expr1->getEval() >= _expr2->getEval()) { return; }
                _expr1->incr(generator);
                _expr2->decr(generator);
            }
        }
        
        void LessThanOrEqualCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            if(!negated){               // less than or equal
                if(_expr1->getEval() <= _expr2->getEval()) { return; }
                _expr1->decr(generator);
                _expr2->incr(generator);
            } else {                    // greater than
                if(_expr1->getEval() > _expr2->getEval()) { return; }
                _expr1->incr(generator);
                _expr2->decr(generator);
            }
        }
        
        void GreaterThanCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            if(!negated){               // greater than
                if(_expr1->getEval() > _expr2->getEval()) { return; }
                _expr1->incr(generator);
                _expr2->decr(generator);
            } else {                    // less than or equal
                if(_expr1->getEval() <= _expr2->getEval()) { return; }
                _expr1->decr(generator);
                _expr2->incr(generator);
            }
        }
        
        void GreaterThanOrEqualCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            if(!negated){               // greater than or equal
                if(_expr1->getEval() >= _expr2->getEval()) { return; }
                _expr1->incr(generator);
                _expr2->decr(generator); 
            } else {                    // less than
                if(_expr1->getEval() < _expr2->getEval()) { return; }
                _expr1->decr(generator);
                _expr2->incr(generator);
            }
        }
        
        void NotCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            _cond->findInteresting(generator, !negated);
        }
        
        void BooleanCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            // Add nothing
        }
        
        void DeadlockCondition::findInteresting(ReducingSuccessorGenerator& generator, bool negated) const {
            if(!isSatisfied()){
                generator.postPresetOf(generator.leastDependentEnabled());
            } // else add nothing
        }
        
        /******************** Just-In-Time Compilation ********************/
    } // PQL
} // PetriEngine

