/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   Expressions.h
 * Author: andreas
 *
 * Created on February 19, 2018, 7:00 PM
 */

#ifndef COLORED_EXPRESSIONS_H
#define COLORED_EXPRESSIONS_H

#include <string>
#include <unordered_map>
#include <set>
#include <stdlib.h>
#include <iostream>
#include <cassert>
#include <memory>


#include "Colors.h"
#include "Multiset.h"

namespace PetriEngine {
    class ColoredPetriNetBuilder;
    
    namespace Colored {
        struct ExpressionContext {
            std::unordered_map<std::string, const Color*>& binding;
            std::unordered_map<std::string, ColorType*>& colorTypes;
            
            const Color* findColor(const std::string& color) const {
                if (color.compare("dot") == 0)
                    return DotConstant::dotConstant();
                for (auto elem : colorTypes) {
                    //printf("Trying color type: %s\n", elem.first.c_str());
                    try {
                        return &(*elem.second)[color];
                    } catch (...) {
//                        for (auto& col : *elem.second) {
//                            //std::cout << col << std::endl;
//                        }
                    }
                }
                printf("Could not find color: %s\nCANNOT_COMPUTE\n", color.c_str());
                exit(-1);
            }
        };
        
        class Expression {
        public:
            Expression() {}
            
            virtual void getVariables(std::set<Variable*>& variables) const {
                //std::cout << "Calling unimplemented getVariables()" << std::endl;
            }
            
            virtual void expressionType() {
                std::cout << "Expression" << std::endl;
            }
        };
        
        class ColorExpression : public Expression {
        public:
            ColorExpression() {}
            virtual ~ColorExpression() {}
            
            virtual const Color* eval(ExpressionContext& context) const = 0;
        };
        
        class DotConstantExpression : public ColorExpression {
        public:
            const Color* eval(ExpressionContext& context) const override {
                return DotConstant::dotConstant();
            }
        };

        typedef std::shared_ptr<ColorExpression> ColorExpression_ptr;
        
        class VariableExpression : public ColorExpression {
        private:
            Variable* _variable;
            
        public:
            const Color* eval(ExpressionContext& context) const override {
                //printf("Binding variable '%s' to color '%s'\n", _variable->name.c_str(), context.binding[_variable->name]->toString().c_str());
                return context.binding[_variable->name];
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                //printf("Getting variable: %s\n", _variable->name.c_str());
                variables.insert(_variable);
            }
            
            VariableExpression(Variable* variable)
                    : _variable(variable) {
                //printf("Creating variable expression with var: %s\n", _variable->name.c_str());
            }
        };
        
        class UserOperatorExpression : public ColorExpression {
        private:
            const Color* _userOperator;
            
        public:
            const Color* eval(ExpressionContext& context) const override {
                return _userOperator;
            }
            
            UserOperatorExpression(const Color* userOperator)
                    : _userOperator(userOperator) {}
        };
        
        class UserSortExpression : public Expression {
        private:
            ColorType* _userSort;
            
        public:
            ColorType* eval(ExpressionContext& context) const {
                return _userSort;
            }
            
            UserSortExpression(ColorType* userSort)
                    : _userSort(userSort) {}
        };

        typedef std::shared_ptr<UserSortExpression> UserSortExpression_ptr;
        
        class NumberConstantExpression : public Expression {
        private:
            uint32_t _number;
            
        public:
            uint32_t eval(ExpressionContext& context) const {
                return _number;
            }
            
            NumberConstantExpression(uint32_t number)
                    : _number(number) {}
        };

        typedef std::shared_ptr<NumberConstantExpression> NumberConstantExpression_ptr;
        
        class SuccessorExpression : public ColorExpression {
        private:
            ColorExpression_ptr _color;
            
        public:
            const Color* eval(ExpressionContext& context) const override {
                return &++(*_color->eval(context));
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _color->getVariables(variables);
            }
            
            SuccessorExpression(ColorExpression_ptr color)
                    : _color(color) {}
        };
        
        class PredecessorExpression : public ColorExpression {
        private:
            ColorExpression_ptr _color;
            
        public:
            const Color* eval(ExpressionContext& context) const override {
                return &--(*_color->eval(context));
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _color->getVariables(variables);
            }
            
            PredecessorExpression(ColorExpression_ptr color)
                    : _color(color) {}
        };
        
        class TupleExpression : public ColorExpression {
        private:
            std::vector<ColorExpression_ptr> _colors;
            
        public:
            const Color* eval(ExpressionContext& context) const override {
                std::vector<const Color*> colors;
                for (auto color : _colors) {
                    colors.push_back(color->eval(context));
                }
                return context.findColor(Color::toString(colors));
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                for (auto elem : _colors) {
                    elem->getVariables(variables);
                }
            }
            
            TupleExpression(std::vector<ColorExpression_ptr> colors)
                    : _colors(colors) {}
        };
        
        class GuardExpression : public Expression {
        public:
            GuardExpression() {}
            virtual ~GuardExpression() {}
            
            virtual bool eval(ExpressionContext& context) const = 0;
        };

        typedef std::shared_ptr<GuardExpression> GuardExpression_ptr;
        
        class LessThanExpression : public GuardExpression {
        private:
            ColorExpression_ptr _left;
            ColorExpression_ptr _right;
            
        public:
            bool eval(ExpressionContext& context) const override {
                return _left->eval(context) < _right->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _left->getVariables(variables);
                _right->getVariables(variables);
            }
            
            LessThanExpression(ColorExpression_ptr left, ColorExpression_ptr right)
                    : _left(left), _right(right) {}
        };
        
        class GreaterThanExpression : public GuardExpression {
        private:
            ColorExpression_ptr _left;
            ColorExpression_ptr _right;
            
        public:
            bool eval(ExpressionContext& context) const override {
                return _left->eval(context) > _right->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _left->getVariables(variables);
                _right->getVariables(variables);
            }
            
            GreaterThanExpression(ColorExpression_ptr left, ColorExpression_ptr right)
                    : _left(left), _right(right) {}
        };
        
        class LessThanEqExpression : public GuardExpression {
        private:
            ColorExpression_ptr _left;
            ColorExpression_ptr _right;
            
        public:
            bool eval(ExpressionContext& context) const override {
                return _left->eval(context) <= _right->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _left->getVariables(variables);
                _right->getVariables(variables);
            }
            
            LessThanEqExpression(ColorExpression_ptr left, ColorExpression_ptr right)
                    : _left(left), _right(right) {}
        };
        
        class GreaterThanEqExpression : public GuardExpression {
        private:
            ColorExpression_ptr _left;
            ColorExpression_ptr _right;
            
        public:
            bool eval(ExpressionContext& context) const override {
                return _left->eval(context) >= _right->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _left->getVariables(variables);
                _right->getVariables(variables);
            }
            
            GreaterThanEqExpression(ColorExpression_ptr left, ColorExpression_ptr right)
                    : _left(left), _right(right) {}
        };
        
        class EqualityExpression : public GuardExpression {
        private:
            ColorExpression_ptr _left;
            ColorExpression_ptr _right;
            
        public:
            bool eval(ExpressionContext& context) const override {
                return _left->eval(context) == _right->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _left->getVariables(variables);
                _right->getVariables(variables);
            }
            
            EqualityExpression(ColorExpression_ptr left, ColorExpression_ptr right)
                    : _left(left), _right(right) {}
        };
        
        class InequalityExpression : public GuardExpression {
        private:
            ColorExpression_ptr _left;
            ColorExpression_ptr _right;
            
        public:
            bool eval(ExpressionContext& context) const override {
                return _left->eval(context) != _right->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _left->getVariables(variables);
                _right->getVariables(variables);
            }
            
            InequalityExpression(ColorExpression_ptr left, ColorExpression_ptr right)
                    : _left(left), _right(right) {}
        };
        
        class NotExpression : public GuardExpression {
        private:
            GuardExpression_ptr _expr;
            
        public:
            bool eval(ExpressionContext& context) const override {
                return !_expr->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _expr->getVariables(variables);
            }
            
            NotExpression(GuardExpression_ptr expr) : _expr(expr) {}
        };
        
        class AndExpression : public GuardExpression {
        private:
            GuardExpression_ptr _left;
            GuardExpression_ptr _right;
            
        public:
            bool eval(ExpressionContext& context) const override {
                return _left->eval(context) && _right->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _left->getVariables(variables);
                _right->getVariables(variables);
            }
            
            AndExpression(GuardExpression_ptr left, GuardExpression_ptr right)
                    : _left(left), _right(right) {}
        };
        
        class OrExpression : public GuardExpression {
        private:
            GuardExpression_ptr _left;
            GuardExpression_ptr _right;
            
        public:
            bool eval(ExpressionContext& context) const override {
                return _left->eval(context) || _right->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _left->getVariables(variables);
                _right->getVariables(variables);
            }
            
            OrExpression(GuardExpression_ptr left, GuardExpression_ptr right)
                    : _left(left), _right(right) {}
        };
        
        class ArcExpression : public Expression {
        public:
            ArcExpression() {}
            virtual ~ArcExpression() {}
            
            virtual Multiset eval(ExpressionContext& context) const = 0;

            virtual void expressionType() override {
                std::cout << "ArcExpression" << std::endl;
            }

            virtual uint32_t weight() const = 0;
        };

        typedef std::shared_ptr<ArcExpression> ArcExpression_ptr;
        
        class AllExpression : public Expression {
        private:
            ColorType* _sort;
            
        public:
            std::vector<const Color*> eval(ExpressionContext& context) const {
                std::vector<const Color*> colors;
                assert(_sort != nullptr);
                for (size_t i = 0; i < _sort->size(); i++) {
                    colors.push_back(&(*_sort)[i]);
                }
                return colors;
            }

            size_t size() const {
                return  _sort->size();
            }
            
            AllExpression(ColorType* sort) : _sort(sort) 
            {
                assert(sort != nullptr);
            }
        };

        typedef std::shared_ptr<AllExpression> AllExpression_ptr;
        
        class NumberOfExpression : public ArcExpression {
        private:
            uint32_t _number;
            std::vector<ColorExpression_ptr> _color;
            AllExpression_ptr _all;
            
        public:
            Multiset eval(ExpressionContext& context) const override {
                std::vector<const Color*> colors;
                if (!_color.empty()) {
                    for (auto elem : _color) {
                        colors.push_back(elem->eval(context));
                    }
                } else if (_all != nullptr) {
                    colors = _all->eval(context);
                }
                std::vector<std::pair<const Color*,uint32_t>> col;
                for (auto elem : colors) {
                    col.push_back(std::make_pair(elem, _number));
                }
                return Multiset(col);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                if (_all != nullptr)
                    return;
                for (auto elem : _color) {
                    elem->getVariables(variables);
                }
            }

            uint32_t weight() const override {
                if (_all == nullptr)
                    return _number * _color.size();
                else
                    return _number * _all->size();
            }

            NumberOfExpression(std::vector<ColorExpression_ptr> color, uint32_t number = 1)
                    : _number(number), _color(color), _all(nullptr) {}
            NumberOfExpression(AllExpression_ptr all, uint32_t number = 1)
                    : _number(number), _color(), _all(all) {}
        };

        typedef std::shared_ptr<NumberOfExpression> NumberOfExpression_ptr;
        
        class AddExpression : public ArcExpression {
        private:
            std::vector<ArcExpression_ptr> _constituents;
            
        public:
            Multiset eval(ExpressionContext& context) const override {
                Multiset ms;
                for (auto expr : _constituents) {
                    ms += expr->eval(context);
                }
                return ms;
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                for (auto elem : _constituents) {
                    elem->getVariables(variables);
                }
            }

            uint32_t weight() const override {
                uint32_t res = 0;
                for (auto expr : _constituents) {
                    res += expr->weight();
                }
                return res;
            }

            AddExpression(std::vector<ArcExpression_ptr> constituents)
                    : _constituents(constituents) {}
        };
        
        class SubtractExpression : public ArcExpression {
        private:
            ArcExpression_ptr _left;
            ArcExpression_ptr _right;
            
        public:
            Multiset eval(ExpressionContext& context) const override {
                return _left->eval(context) - _right->eval(context);
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _left->getVariables(variables);
                _right->getVariables(variables);
            }

            uint32_t weight() const override {
                return _left->weight() - _right->weight();
            }

            SubtractExpression(ArcExpression_ptr left, ArcExpression_ptr right)
                    : _left(left), _right(right) {}
        };
        
        class ScalarProductExpression : public ArcExpression {
        private:
            uint32_t _scalar;
            ArcExpression_ptr _expr;
            
        public:
            Multiset eval(ExpressionContext& context) const override {
                return _expr->eval(context) * _scalar;
            }
            
            void getVariables(std::set<Variable*>& variables) const override {
                _expr->getVariables(variables);
            }

            uint32_t weight() const override {
                return _scalar * _expr->weight();
            }

            ScalarProductExpression(ArcExpression_ptr expr, uint32_t scalar)
                    : _scalar(scalar), _expr(expr) {}
        };
    }
}

#endif /* COLORED_EXPRESSIONS_H */
