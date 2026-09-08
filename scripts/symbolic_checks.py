#!/usr/bin/env python3
"""Exact symbolic diagnostics. These are not Lean/kernel certificates."""
import json
import sympy as s

u, e, U, E = s.symbols('u e U E', positive=True)
n, x, a = s.symbols('n x a', real=True)
assert s.factor(u*u/U + e*e/E - (u+e)**2/(U+E)
                - (E*u-U*e)**2/((U+E)*U*E)) == 0
assert s.factor((n-2)*(1-x)-(n*a-1)
                - n/s.Integer(2)*(1-2*a-(n-2)/n*x*x)
                - (n-2)/s.Integer(2)*(1-x)**2) == 0
V = s.Matrix([[1,0],[0,1],[-s.Rational(3,5),s.Rational(4,5)]])
G = V*V.T
assert G == s.Matrix([[1,0,-s.Rational(3,5)],
                     [0,1,s.Rational(4,5)],
                     [-s.Rational(3,5),s.Rational(4,5),1]])
assert G.rank() == 2 and G.det() == 0
t = s.symbols('t', positive=True)
pins = {}
for i,j in [(0,1),(0,2),(1,2)]:
    c=G[i,j]
    alpha=(G[:,i]-c*G[:,j])/(1-c*c)
    beta=(G[:,j]-c*G[:,i])/(1-c*c)
    ei=s.eye(3)[:,i]; ej=s.eye(3)[:,j]
    P=s.eye(3)-alpha*ei.T-beta*ej.T
    assert P*G[:,i] == s.zeros(3,1)
    assert P*G[:,j] == s.zeros(3,1)
    assert P*G*P.T == s.zeros(3)
    mean=s.simplify((alpha+beta)*t)
    k=({0,1,2}-{i,j}).pop()
    pins[f'{i},{j}']={'remaining':k,'mean_over_t':str(s.simplify(mean[k]/t))}
assert pins['0,1']['mean_over_t']=='1/5'
assert pins['0,2']['mean_over_t']=='2'
assert pins['1,2']['mean_over_t']=='-1/3'
q01,q02,q12=s.symbols('q01 q02 q12', real=True)
Q=s.Matrix([[0,q01,q02],[q01,0,q12],[q02,q12,0]])
S=Q.copy()
for i in range(3): S[i,i]=-sum(G[i,j]*Q[i,j] for j in range(3) if j!=i)
assert s.expand(s.trace(S*G))==0
L=s.diag(0,0,1)
assert s.expand(s.trace(S*L)/2).subs(q02,0)==-s.Rational(2,5)*q12
# General 3-coordinate generator cancellation, with arbitrary symmetric L, G and q.
c01,c02,c12=s.symbols('c01 c02 c12')
C=s.Matrix([[1,c01,c02],[c01,1,c12],[c02,c12,1]])
h0,h1,h2=s.symbols('h0 h1 h2'); h=[h0,h1,h2]
l0,l1,l2,l01,l02,l12=s.symbols('l0 l1 l2 l01 l02 l12')
L=s.Matrix([[l0,l01,l02],[l01,l1,l12],[l02,l12,l2]])
B=Q.copy(); SS=Q.copy()
for i in range(3):
    SS[i,i]=-sum(C[i,j]*Q[i,j] for j in range(3) if j!=i)
    B[i,i]=-t*h[i]+SS[i,i]
left=(sum(t*L[i,i]*h[i] for i in range(3))+s.trace(L*B))/2
assert s.expand(left-s.trace(SS*L)/2)==0
print(json.dumps({'status':'all exact symbolic assertions passed',
                  'sympy_version':s.__version__,
                  'triangle_gram':str(G), 'rank':G.rank(),
                  'deterministic_pair_pins':pins,
                  'rank_lifting_derivative_after_q02_zero':'-2*q12/5',
                  'limits':'No probability integral, derivative theorem, or Lean proof checked.'},indent=2))
