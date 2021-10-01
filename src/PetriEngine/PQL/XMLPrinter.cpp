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
#include "PetriEngine/PQL/XMLPrinter.h"
namespace PetriEngine {
    namespace PQL {
        std::ostream& XMLPrinter::generateTabs() {
            for(uint32_t i = 0; i < tabs; i++) {
                os << "  ";
            }
            return os;
        }

        void XMLPrinter::openXmlTag(const std::string &tag) {
            generateTabs() << "<" << tag << ">\n";
            tabs++;
        }

        void XMLPrinter::closeXmlTag(const std::string &tag) {
            tabs--;
            generateTabs() << "</" << tag << ">\n";
        }

        void XMLPrinter::_accept(const NotCondition *element) {
            openXmlTag("negation");
            element->getCond()->visit(*this);
            closeXmlTag("negation");
        }

        void XMLPrinter::_accept(const AndCondition *element) {
            if(element->empty())
            {
                BooleanCondition::TRUE_CONSTANT->visit(*this);
                return;
            }
            if(element->size() == 1)
            {
                (*element)[0]->visit(*this);
                return;
            }
            openXmlTag("conjunction");
            (*element)[0]->visit(*this);
            for(size_t i = 1; i < element->size(); ++i)
            {
                if(i + 1 == element->size())
                {
                    (*element)[i]->visit(*this);
                }
                else
                {
                    openXmlTag("conjunction");
                    (*element)[i]->visit(*this);
                }
            }
            for(size_t i = element->size() - 1; i > 1; --i)
            {
                closeXmlTag("conjunction");
            }
            closeXmlTag("conjunction");
        }

        void XMLPrinter::_accept(const OrCondition *element) {
            if(element->empty())
            {
                BooleanCondition::FALSE_CONSTANT->visit(*this);
                return;
            }
            if(element->size() == 1)
            {
                (*element)[0]->visit(*this);
                return;
            }
            openXmlTag("disjunction");
            (*element)[0]->visit(*this);
            for(size_t i = 1; i < element->size(); ++i)
            {
                if(i + 1 == element->size())
                {
                    (*element)[i]->visit(*this);
                }
                else
                {
                    openXmlTag("disjunction");
                    (*element)[i]->visit(*this);
                }
            }
            for(size_t i = element->size() - 1; i > 1; --i)
            {
                closeXmlTag("disjunction");
            }
            closeXmlTag("disjunction");
        }

        void XMLPrinter::_accept(const LessThanCondition *element) {
            openXmlTag("integer-lt");
            (*element)[0]->visit(*this);
            (*element)[1]->visit(*this);
            closeXmlTag("integer-lt");
        }

        void XMLPrinter::_accept(const LessThanOrEqualCondition *element) {
            openXmlTag("integer-le");
            (*element)[0]->visit(*this);
            (*element)[1]->visit(*this);
            closeXmlTag("integer-le");
        }

        void XMLPrinter::_accept(const EqualCondition *element) {
            openXmlTag("integer-eq");
            (*element)[0]->visit(*this);
            (*element)[1]->visit(*this);
            closeXmlTag("integer-eq");
        }

        void XMLPrinter::_accept(const NotEqualCondition *element) {
            openXmlTag("integer-ne");
            (*element)[0]->visit(*this);
            (*element)[1]->visit(*this);
            closeXmlTag("integer-ne");
        }

        void XMLPrinter::_accept(const DeadlockCondition *element) {
            generateTabs() << "<deadlock/>\n";
        }

        void XMLPrinter::_accept(const CompareConjunction *element) {
            if(element->isNegated()) {
                generateTabs() << "<negation>";
            }

            if(element->constraints().empty()) BooleanCondition::TRUE_CONSTANT->visit(*this);
            else
            {
                bool single = element->constraints().size() == 1 &&
                              (element->constraints()[0]._lower == 0 ||
                               element->constraints()[0]._upper == std::numeric_limits<uint32_t>::max());
                if(!single)
                    openXmlTag("conjunction");
                for(auto& c : element->constraints())
                {
                    if(c._lower != 0)
                    {
                        openXmlTag("integer-ge");
                        openXmlTag("tokens-count");
                        generateTabs() << "<place>" << c._name << "</place>\n";
                        closeXmlTag("tokens-count");
                        generateTabs() << "<integer-constant>" << c._lower << "</integer-constant>\n";
                        closeXmlTag("integer-ge");
                    }
                    if(c._upper != std::numeric_limits<uint32_t>::max())
                    {
                        openXmlTag("integer-le");
                        openXmlTag("tokens-count");
                        generateTabs() << "<place>" << c._name << "</place>\n";
                        closeXmlTag("tokens-count");
                        generateTabs() << "<integer-constant>" << c._upper << "</integer-constant>\n";
                        closeXmlTag("integer-le");
                    }
                }
                if(!single)
                    closeXmlTag("conjunction");
            }
            if(element->isNegated()) {
                generateTabs() << "</negation>";
            }
        }

        void XMLPrinter::_accept(const UnfoldedUpperBoundsCondition *element) {
            openXmlTag("place-bound");
            for(auto& p : element->places()) {
                generateTabs() << "<place>" << p._name << "</place>\n";
            }
            closeXmlTag("place-bound");
        }

        void XMLPrinter::_accept(const EFCondition *condition) {
            openXmlTag("exists-path");
            openXmlTag("finally");
            condition->getCond()->visit(*this);
            closeXmlTag("finally");
            closeXmlTag("exists-path");
        }

        void XMLPrinter::_accept(const EGCondition *condition) {
            openXmlTag("exists-path");
            openXmlTag("globally");
            condition->getCond()->visit(*this);
            generateTabs() <<  "</globally>\n" ;
            closeXmlTag("exists-path");
        }

        void XMLPrinter::_accept(const AGCondition *condition) {
            openXmlTag("all-paths");
            openXmlTag("globally");
            condition->getCond()->visit(*this);
            closeXmlTag("globally");
            closeXmlTag("all-paths");
        }

        void XMLPrinter::_accept(const AFCondition *condition) {
            openXmlTag("all-paths");
            openXmlTag("finally");
            condition->getCond()->visit(*this);
            closeXmlTag("finally");
            closeXmlTag("all-paths");
        }

        void XMLPrinter::_accept(const EXCondition *condition) {
            openXmlTag("exists-path");
            openXmlTag("next");
            condition->getCond()->visit(*this);
            closeXmlTag("next");
            closeXmlTag("exists-path");
        }

        void XMLPrinter::_accept(const AXCondition *condition) {
            openXmlTag("all-paths");
            openXmlTag("next");
            condition->getCond()->visit(*this);
            closeXmlTag("next");
            closeXmlTag("all-paths");
        }

        void XMLPrinter::_accept(const EUCondition *condition) {
            openXmlTag("exists-path");
            openXmlTag("until");
            openXmlTag("before");
            (*condition)[0]->visit(*this);
            closeXmlTag("before");
            openXmlTag("reach");
            (*condition)[1]->visit(*this);
            closeXmlTag("reach");
            closeXmlTag("until");
            closeXmlTag("exists-path");
        }

        void XMLPrinter::_accept(const AUCondition *condition) {
            openXmlTag("all-paths");
            openXmlTag("until");
            openXmlTag("before");
            (*condition)[0]->visit(*this);
            closeXmlTag("before");
            openXmlTag("reach");
            (*condition)[1]->visit(*this);
            closeXmlTag("reach");
            closeXmlTag("until");
            closeXmlTag("all-paths");

        }

        void XMLPrinter::_accept(const ACondition *condition) {
            openXmlTag("all-paths");
            condition->getCond()->visit(*this);
            closeXmlTag("all-paths");
        }

        void XMLPrinter::_accept(const ECondition *condition) {
            openXmlTag("exists-path");
            condition->getCond()->visit(*this);
            closeXmlTag("exists-path");
        }

        void XMLPrinter::_accept(const GCondition *condition) {
            openXmlTag("globally");
            condition->getCond()->visit(*this);
            closeXmlTag("globally");
        }

        void XMLPrinter::_accept(const FCondition *condition) {
            openXmlTag("finally");
            condition->getCond()->visit(*this);
            closeXmlTag("finally");
        }

        void XMLPrinter::_accept(const XCondition *condition) {
            openXmlTag("next");
            condition->getCond()->visit(*this);
            closeXmlTag("next");
        }

        void XMLPrinter::_accept(const UntilCondition *condition) {
            openXmlTag("until") ;
            openXmlTag("before");
            (*condition)[0]->visit(*this);
            closeXmlTag("before") ;
            openXmlTag("reach");
            (*condition)[1]->visit(*this);
            closeXmlTag("reach") ;
            closeXmlTag("until") ;
        }

        void XMLPrinter::_accept(const UnfoldedFireableCondition *element) {
            generateTabs() << "<is-fireable><transition>" + element->getName() << "</transition></is-fireable>\n";
        }

        void XMLPrinter::_accept(const BooleanCondition *element) {
            generateTabs() << "<" << (element->value ? "true" : "false") << "/>\n";
        }

        void XMLPrinter::_accept(const UnfoldedIdentifierExpr *element) {
            if (token_count) {
                generateTabs() << "<place>" << element->name() << "</place>\n";
            }
            else
            {
                openXmlTag("tokens-count");
                generateTabs() << "<place>" << element->name() << "</place>\n";
                closeXmlTag("tokens-count");
            }
        }

        void XMLPrinter::_accept(const LiteralExpr *element) {
            generateTabs() << "<integer-constant>" + std::to_string(element->value()) + "</integer-constant>\n";
        }

        void XMLPrinter::_accept(const PlusExpr *element) {
            if (token_count) {
                for(auto& e : element->expressions())
                    e->visit(*this);
                return;
            }

            if(element->tk) {
                openXmlTag("tokens-count");
                for(auto& e : element->places())
                    generateTabs() << "<place>" << e.second << "</place>\n";
                for(auto& e : element->expressions())
                    e->visit(*this);
                closeXmlTag("tokens-count");
                return;
            }
            openXmlTag("integer-sum");
            generateTabs() << "<integer-constant>" + std::to_string(element->constant()) + "</integer-constant>\n";
            for(auto& i : element->places())
            {
                openXmlTag("tokens-count");
                generateTabs() << "<place>" << i.second << "</place>\n";
                closeXmlTag("tokens-count");
            }
            for(auto& e : element->expressions())
                e->visit(*this);
            closeXmlTag("integer-sum");
        }

        void XMLPrinter::_accept(const MultiplyExpr *element) {
            openXmlTag("integer-product");
            for(auto& e : element->expressions())
                e->visit(*this);
            closeXmlTag("integer-product");
        }

        void XMLPrinter::_accept(const MinusExpr *element) {
            openXmlTag("integer-product");
            (*element)[0]->visit(*this);
            openXmlTag("integer-difference");
            generateTabs() << "<integer-constant>0</integer-constant>\n";
            generateTabs() << "<integer-constant>1</integer-constant>\n";
            closeXmlTag("integer-difference");
            closeXmlTag("integer-product");
        }

        void XMLPrinter::_accept(const SubtractExpr *element) {
            openXmlTag("integer-difference");
            for(auto& e : element->expressions())
                e->visit(*this);
            closeXmlTag("integer-difference");
        }

        void XMLPrinter::_accept(const IdentifierExpr *element) {
            if (token_count) {
                generateTabs() << "<place>" << element->name() << "</place>\n";
            }
            else
            {
                openXmlTag("tokens-count");
                generateTabs() << "<place>" << element->name() << "</place>\n";
                closeXmlTag("tokens-count");
            }
        }
    }
}

