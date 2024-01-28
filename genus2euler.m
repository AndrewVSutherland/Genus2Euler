/*
    This magma package file implements the algorithms described in the paper

        Computing Euler factors of genus 2 curves over Q at primes of almost good reduction
        by Celine Maistret and Andrew V. Sutherland
*/

lpoly3 := func<f|LPolynomial(EllipticCurve(Evaluate(f,Parent(f).1/c)*c^2)) where c:=LeadingCoefficient(f)>;
vc := func<g,p|v where v,_:=Valuation(LeadingCoefficient(g),p)>;
irred := func<d,R|&cat[[R|f:cc in CartesianPower(F,i)|IsIrreducible(f) where f:=R!([c:c in TupleToList(cc)] cat [F|1])]:i in [1..d]] where F:=BaseRing(R)>;
gcd := func<f,k|(Characteristic(BaseRing(R)) gt 5 select GCD([Derivative(f,i):i in [0..k-1]])
                else &*[R|g^(Valuation(f,g)-k+1):g in irred(Degree(f) div k,R)|Valuation(f,g) ge k]) where R:=Parent(f)>;
gcd3 := func<f|gcd(f,3)>;  gcd5 := func<f|gcd(f,5)>; gcd6 := func<f|gcd(f,6)>;

// Implementation of Algorithm 3 (type 1) in the paper
function Type1(f,p)
    ZZ := Integers(); R<T> := PolynomialRing(ZZ); Fp:=GF(p); Rp<t>:=PolynomialRing(Fp);  f:=R!f;  fp := ChangeRing(f,Fp);
    gp := gcd3(fp); assert Degree(gp) eq 1;
    fp := Evaluate(fp,t-Coefficient(gp,0));                 // fp(t+r) is a sextic divisible by t^3
    L := [lpoly3(Rp![Coefficient(fp,6-i):i in [0..3]])];    // Reverse coefficients of fp(t+r)/t^2 to get a cubic
    r := ZZ!-Coefficient(gp,0); i := 1;
    while true do
        f := ExactQuotient(Evaluate(f,p*T+r),p^3); fp := ChangeRing(f,Fp); assert Degree(fp) eq 3;
        if IsEven(i) and Discriminant(fp) ne 0 then L[2] := lpoly3(fp); break; end if; // per Remark 4.7, we only check even i
        gp := gcd3(fp); assert Degree(gp) eq 1;
        r := ZZ!-Coefficient(gp,0); i +:= 1;
    end while;
    return R!&*L;
end function;

// Implementation of Algorithm 4 (type 2a) in the paper
function Type2a(f,p)
    ZZ:=Integers(); R<T>:=PolynomialRing(ZZ); Fp:=GF(p); Rp<t>:=PolynomialRing(Fp); f:=R!f;
    f := vc(f,p) eq 1 select ExactQuotient(f,p) else f;  fp := ChangeRing(f,Fp);
    gp := gcd3(fp);  assert Degree(gp) eq 2;
    d := SquareRoot(Discriminant(gp)); // non-deterministic step that can be made deterministic given a non-residue
    rr := [Fp|(-b + d)/2,(-b-d)/2] where b:=Coefficient(gp,1);
    L := []; f0 := f;
    for i:=1 to 2 do
        r := ZZ!rr[i]; f := f0;
        while true do
            f := ExactQuotient(Evaluate(f,p*T+r),p^3); fp := ChangeRing(f,Fp);  assert Degree(fp) eq 3;
            if Discriminant(fp) ne 0 then L[i] := lpoly3(fp); break; end if;
            gp := gcd3(fp); assert Degree(gp) eq 1;
            r := ZZ!-Coefficient(gp,0);
        end while;
    end for;
    return R!&*L;
end function;

// Implementation of Algorithm 5 (type 2b) in the paper
function Type2b(f,p)
    ZZ:=Integers(); R<T>:=PolynomialRing(ZZ); Fp:=GF(p); Rp<t>:=PolynomialRing(Fp);  f:=R!f;
    f := vc(f,p) eq 1 select ExactQuotient(f,p) else f;  fp := ChangeRing(f,Fp);
    up := gcd3(fp); assert Degree(up) eq 2;  u := ChangeRing(up,Integers());
    K<Z> := quo<R|u>; Kp<z> := quo<Rp|up>; RK<T> := PolynomialRing(K); RKp<t> := PolynomialRing(Kp);
    RKdiv := func<f,d|RK![K![ExactQuotient(c,d):c in Coefficients(fc)]:fc in Coefficients(f)]>;
    RKmod := func<f|RKp![Evaluate(c,z):c in Coefficients(f)]>;  Klift := func<a|K!Eltseq(a)>;
    Fp2 := ext<Fp|up>; Rp2 := PolynomialRing(Fp2); Fp2poly := func<g|Rp2![Fp2!Eltseq(c):c in Coefficients(g)]>;
    f := RK!f; r := Z; L := 0;
    while true do
        f := RKdiv(Evaluate(f,p*T+r),p^3); fp := RKmod(f); assert Degree(fp) eq 3;
        if Discriminant(fp) ne 0 then L := lpoly3(Fp2poly(fp)); break; end if;
        gp := gcd3(fp); assert Degree(gp) eq 1;
        r := Klift(-Coefficient(gp,0));
    end while;
    return Evaluate(L,T^2);
end function;

// Implementation of Algorithm 6 (type 4) in the paper
function Type4(f,p)
    ZZ := Integers(); R<T> := PolynomialRing(ZZ); Fp:=GF(p); Rp<t> := PolynomialRing(Fp);  f:=R!f;
    f := IsDivisibleBy(f,p) select ExactQuotient(f,p) else f; fp := ChangeRing(f,Fp);
    gp := gcd5(fp); assert Degree(gp) eq 1;
    r := ZZ!-Coefficient(gp,0); L := [];
    while true do
        f := ExactQuotient(Evaluate(f,p*T+r),p^5); fp := ChangeRing(f,Fp); assert Degree(fp) eq 5;
        gp := gcd3(fp);
        if Degree(gp) eq 1 then
            r := ZZ!-Coefficient(gp,0);
            gp := ExactQuotient(fp,gp^2); assert Discriminant(gp) ne 0;
            L := [lpoly3(gp)]; break;
        end if;
        gp := gcd5(fp); assert Degree(gp) eq 1;
        r := ZZ!-Coefficient(gp,0);
    end while;
    while true do
        f := ExactQuotient(Evaluate(f,p*T+r),p^3); fp := ChangeRing(f,Fp); assert Degree(fp) eq 3;
        if Discriminant(fp) ne 0 then L[2] := lpoly3(fp); break; end if;
        gp := gcd3(fp); assert Degree(gp) eq 1;
        r := ZZ!-Coefficient(gp,0);
    end while;
    return &*L;
end function;

// Implementation of Algorithm 2 (which type) in the paper
function WhichType(f,p)
    assert Degree(f) eq 6 and p gt 2;
    ZZ := Integers(); R<T> := PolynomialRing(ZZ); Fp:=GF(p); Rp<t> := PolynomialRing(Fp);  f := R!f;
    fp := ChangeRing(vc(f,p) gt 0 select ExactQuotient(f,p^vc(f,p)) else f,Fp);
    gp := gcd3(fp); assert Degree(gp) in [1,2,3];
    if Degree(gp) eq 2 then return (IsSquare(Discriminant(gp)) select 2 else 3), gp; end if;
    return (Degree(gp) eq 1 select 1 else 4), gp; // Degree(gp) eq 3 in type 4 case
end function;

// Implementation of Algorithm 1 (normalize) in the paper
function Normalize(f,p)
    assert Degree(f) ge 5 and p gt 2;
    ZZ := Integers(); R<T> := PolynomialRing(ZZ); Fp:=GF(p); Rp<t> := PolynomialRing(Fp);  f := R!f;
    if Degree(f) lt 6 then
        while Coefficient(f,0) eq 0 do f:=Evaluate(f,T+1); end while;
        f := R![Coefficient(f,6-i):i in [0..6]];  assert Degree(f) eq 6;
    end if;
    v := vc(f,p);
    if v gt 1 or v gt Min([Valuation(Coefficient(f,i),p):i in [0..5]]) then
        e := Max([Ceiling((v-Valuation(Coefficient(f,i),p))/(6-i)):i in [0..5]]);
        f := R![p^((6-i)*e-w)*Coefficient(f,i):i in [0..6]] where w := 2*(v div 2);  v := vc(f,p);
    end if;
    h := ExactQuotient(f,p^v);
    while true do
        up := gcd6(ChangeRing(h,Fp)); if Degree(up) eq 0 then break; end if;
        h := ExactQuotient(Evaluate(h,p*T+r),p^6) where r:=ZZ!-Coefficient(up,0);
    end while;
    return p^v*h;
end function;

// Implementation of Algorithm 7 (main) in the paper as a Magma intrinsic
intrinsic Genus2GoodEulerFactor(f::RngUPolElt[RngInt],p::RngIntElt:WhichCaseOnly:=false) -> RngUPolElt[RngInt], RngIntElt
{ returns the Euler factor of the genus 2 curve C:y^2=f(x) at an odd prime of almost good reduction (bad for C but, good for Jac(C)). }
    require Degree(f) in [5,6]: "f should be a squarefree polynomial of degree 5 or 6"; // we don't verify that f is squarefree
    if p eq 2 then return EulerFactor(HyperellipticCurve(f),p); end if; // revert to Magma for p=2
    f := Normalize(f,p);
    n := WhichType(f,p);
    if WhichCaseOnly then return n; end if;
    if n eq 1 then return Type1(f,p);
    elif n eq 2 then return Type2a(f,p);   // we use 2 to indicate 2a
    elif n eq 3 then return Type2b(f,p);   // we use 3 to indicate 2b
    elif n eq 4 then return Type4(f,p);
    end if;
    assert false; // we should never reach this line
end intrinsic;

// The intrinsics below provide polymorphic interfaces to the Genus2GoodEulerFactor intrinsic above

intrinsic Genus2GoodEulerFactor(f::RngUPolElt[FldRat],p::RngIntElt:WhichCaseOnly:=false) -> RngUPolElt[RngInt], RngIntElt
{ returns the Euler factor of the genus 2 curve C:y^2=f(x) at an odd prime of almost good reduction (bad for C but, good for Jac(C)). }
    return Genus2GoodEulerFactor(ChangeRing(f,Integers()),p:WhichCaseOnly:=WhichCaseOnly);
end intrinsic;

intrinsic Genus2GoodEulerFactor(f::SeqEnum[RngIntElt],p::RngIntElt:WhichCaseOnly:=false) -> RngUPolElt[RngInt], RngIntElt
{ returns the Euler factor of the genus 2 curve C:y^2=f(x) specified by coeffs(f) at an odd prime of almost good reduction (bad for C but, good for Jac(C)). }
    return Genus2GoodEulerFactor(R!f,p:WhichCaseOnly:=WhichCaseOnly) where R:=PolynomialRing(Integers());
end intrinsic;

intrinsic Genus2GoodEulerFactor(fh::SeqEnum[SeqEnum[RngIntElt]],p::RngIntElt:WhichCaseOnly:=false) -> RngUPolElt[RngInt], RngIntElt
{ returns the Euler factor of the genus 2 curve C:y^2+h(x)y=f(x) specified by [coeffs(f),coeffs(h)] at an odd prime of almost good reduction (bad for C but, good for Jac(C)). }
    require #fh eq 2: "Expected a list of lists of coefficients [coeffs(f),coeffs(h)] for genus 2 curve y^2+h(x)y=f(x).";
    return Genus2GoodEulerFactor((4*R!fh[1]+R!fh[2])^2,p:WhichCaseOnly:=WhichCaseOnly) where R:= PolynomialRing(Integers());
end intrinsic;

intrinsic Genus2GoodEulerFactor(fh::SeqEnum[RngUPolElt],p::RngIntElt:WhichCaseOnly:=false) -> RngUPolElt[RngInt], RngIntElt
{ returns the Euler factor of the genus 2 curve C:y^2+h(x)y=f(x) specified by [f,h] at an odd prime of almost good reduction (bad for C but, good for Jac(C)). }
    return Genus2GoodEulerFactor([Coefficients(f):f in fh],p:WhichCaseOnly:=WhichCaseOnly);
end intrinsic;

intrinsic Genus2GoodEulerFactor(C::CrvHyp,p::RngIntElt:WhichCaseOnly:=false) -> RngUPolElt[RngInt], RngIntElt
{ returns the Euler factor of the genus 2 curve C at an odd prime of  almost good reduction (bad for C but, good for Jac(C)). }
    return Genus2GoodEulerFactor([f,h],p:WhichCaseOnly:=WhichCaseOnly) where f,h := HyperellipticPolynomials(C);
end intrinsic;
