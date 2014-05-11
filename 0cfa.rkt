#lang datalog

% 0CFA analysis
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% This program performs 0CFA analysis on the Lambda Calculus with addition, 
% and returns, for each expression, the smallest set of labels (in 0CFA) the expression can evaluate to.


% The following relations define the possible expressions in the Lambda Calculus
%    const(L)     : The expression at label L is a constant.
%    add(L)       : The expression at label L is the sum of two expressions.
%    var(L,X)     : The expression at label L is the variable X.
%    abs(L,X,B)   : The expression at label L is an abstraction where the
%                   variable is X and the body has label B.
%    app(L,L1,L2) : The expression at label L is an application where the
%                   expression being applied has label L1 and the expression
%                   used as an argument has label L2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% L1 and L2 are in the relation c(L1,L2) if the expression with label L1
% can evaluate to a value with label L2.
c(L1,L2) :- const(L1), L1 = L2.
c(L1,L2) :- add(L1), L1 = L2.
c(L1,L2) :- var(L1,X),  r(X,L2).

% An abstraction may evaluate to itself
c(L1,L2) :- abs (L1,X,E1), L1 = L2.  
% An application may evaluate to the Label of any abstraction that 
% occurs in L1.
c(L,LR) :- app(L,L1,L2), abs(L',X,L0), c(L1,L'), c(L0,LR).

% X and LR are in the relation r(X,LR) if variable X may be bound to
% a value with label LR.
% A variable on the left side of an application 
% may be bound to any Label in the right side of the expression
r(X,LR) :- app(L,L1,L2), abs(L',X,L0), c(L1,L'), c(L2,LR).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TEST CASES
% To Enter a new test create a test set and uncomment it
% Make sure only one test set is uncommented
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ex01.lam
% Expression with location annotations:
% 7: (5: (2: (\a. 1: a) 4: (\b. 3: b)) 6: 99)
% Datalog facts:
% app(7,5,6).
 %app(5,2,4).
 %abs(2,a,1).
 %var(1,a).
 %abs(4,b,3).
 %var(3,b).
 %const(6).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ex02.lam
% Expression with location annotations:
% 9: (4: (\x. 3: (1: x 2: x)) 8: (\y. 7: (5: y 6: y)))
% Datalog facts:
% app(9,4,8).
% abs(4,x,3).
% app(3,1,2).
% var(1,x).
% var(2,x).
% abs(8,y,7).
% app(7,5,6).
% var(5,y).
% var(6,y).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ex03.lam
% Expression with location annotations:
% 9: (4: (\x. 3: (1: x 2: x)) 8: (\x. 7: (5: x 6: x)))
% Datalog facts:
 %app(9,4,8).
 %abs(4,x,3).
 %app(3,1,2).
 %var(1,x).
 %var(2,x).
 %abs(8,x,7).
 %app(7,5,6).
 %var(5,x).
 %var(6,x).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Expression with location annotations:
%
% 9: (6: (\id. 5: (3: (1: id 2: id) 4: 7)) 8: (\x. 7: x))
%
% Datalog facts:
app(9,6,8).
abs(6,id,5).
app(5,3,4).
app(3,1,2).
var(1,id).
var(2,id).
const(4).
abs(8,x,7).
var(7,x).