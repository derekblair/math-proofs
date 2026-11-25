# No quadratic proper lifting on the binary shift

This answers Section 4(iii) of Jan Kristian Haugland and Tron Omland, *New classes of reversible cellular automata*, [arXiv:2411.00721v2](https://arxiv.org/pdf/2411.00721). The preprint's first version listed this as Question 2.3. Houqiao Fu, [arXiv:2609.35921](https://arxiv.org/abs/2609.35921), proved a stronger guarantee on which ring lengths have collisions for the special case of five-slot rules. The present proof applies to all finite widths.

## Exact statement
For every local Boolean rule in algebraic normal form, with constant, linear, and quadratic terms only, suppose that applying the same rule at every position around each ring of size n at least the window width gives a bijection. Then every quadratic coefficient is zero. Thus a rule of exact algebraic degree two cannot be a proper lifting. The theorem is QuadraticCA.no_degree_two_proper_lifting, in QuadraticAnswer.lean. There is no assumption on the position of the active variables or the window width. No premise relies on a computation over a bounded set of candidate rules.

## Proof
Write F for the shift-equivariant map induced by the local rule and D for the adjacent-bit difference, D(x)(i)=x(i)+x(i+1), over the field of two elements. Finite-ring injectivity implies injectivity on streams of any common positive period, by repeating to a large enough ring. Distinct constant streams therefore have distinct images.

1. For a quadratic rule the polar form B(x,y)=F(x+y)+F(x)+F(y)+F(0) is bilinear. The map L(x)=B(x,1) is a local linear operator commuting with D. If L is nonzero, it is nonzero at some stream of period N a power of two, since any finite window extends to such a stream. On streams of period N, D iterated N times vanishes: in characteristic two, (1+S)^N=1+S^N for the shift S. Thus the last nonzero iterate of L(x) under D is a nonzero constant, necessarily 1. Commuting gives L(z)=1 for a periodic z, so F(z+1)=F(z), impossible. Consequently F commutes with global bit complement.
2. Adjacent-bit differences now give a quotient rule G, with G(Dx)=D(Fx). Integrate a difference stream by cumulative sums. A period-n difference stream has a period-2n integral, and equal output differences mean the two outputs differ by a constant. Complement equivariance and injectivity of F then show that G is injective on periodic streams. Every output of G reads only finitely many consecutive difference bits, because two possible initial phases of the integral differ by a complement which vanishes under D. Its polar form is bilinear, by surjectivity and additivity of D and the identity B_G(Dx,Dy)=D(B_F(x,y)).
3. Induct on r, simultaneously for every such rule, that B_F(x,y)=0 if D iterated r times kills x and y is eventually zero. The step follows by applying the induction hypothesis to G, Dx and Dy: D(B_F(x,y))=0. The polar stream is constant and eventually zero by locality, hence zero everywhere. Any pair of local windows has extensions of these types, with x power-of-two periodic and y eventually zero. Therefore the local polar form vanishes. Evaluating it on two different coordinate impulses reads off the corresponding quadratic coefficient.

## Verification
With Lean 4.34.1 on PATH and a Mathlib v4.34.1 checkout (commit d13f23b723b8a846827a245b89c10fc7d3f11612 with its build cache), run:
 
    ./verify.sh /path/to/mathlib4

This compiles the seven modules in a fresh temporary directory and independently replays each with leanchecker. See verification.log. The only axiom dependencies of the main theorem are propext, Classical.choice, and Quot.sound. Controls.lean checks a genuinely proper affine rule, and independently checks a direct finite-ring collision for a quadratic monomial. Optional controls.py uses only standard Python and does not enter the Lean proof.
