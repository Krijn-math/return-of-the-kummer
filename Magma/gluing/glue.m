/*
    This file verifies the result on glueing in section 2. It shows that,
    when glued correctly, we get a (2,2)-isogeny E x E^(p) --> Jac(C) over Fp2
    and that the Weil restriction W(E) of E gives us, via Scholten's construction
    a (2,2)-isogeny W(E) --> Jac(C) over Fp, for the same curve C, but with the 
    Jacobian over Fp. Thus, changing the basis of this Jacobian to Fp2 shows they
    are isomorphic and furthermore, the isogenous W(E) surface over Fp becomes
    E x E^(p) over Fp2. 

    Note: any ppav in dimension 2 is isomorphic over kbar to either a product of elliptic
    curves, or the jacobian of a genus 2 (hyperelliptic) curve. However, over k, in this
    case a finite field that is not algebraically closed, there is the third option that
    it is isomorphic to the Weil restriction of an elliptic curve. This is precisely
    the case in our situation. 

    Note: When asking for RichelotIsogenousSurfaces, Magma displays the Weil restriction
    of E as simply E itself, and will not inform you that this is actually the Weil 
    restriction. This may cause confusion at first.
*/

//very ugly hack to ensure we dont overload files
if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "glue.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

k := 20; p := NextPrime(Random([2^k..2^(k+1)]));
repeat p := NextPrime(p); until p mod 4 eq 3;

alpha, E_alpha, Fp, Fp2<i>, poly := SupersingularMontgomeryCurve(p);
C_alpha, J_alpha, beta, gamma, zs := SupersingularAbelianSurfaceFromMontgomeryCurve(alpha);
K := SupersingularKummerSurfaceFromMontgomeryCurve(alpha);
PX<X> := PolynomialRing(Fp);
poly<x>:=PolynomialRing(Fp2);


//the following functions construct the glueing along the right 2-torsion
//derived from Castryck-Decru 2022/975
function firstcoeff(alpha, beta)
    return (alpha[3] - alpha[2])^2/(beta[3] - beta[2]) +
           (alpha[2] - alpha[1])^2/(beta[2] - beta[1]) + 
           (alpha[1] - alpha[3])^2/(beta[1] - beta[3]);
end function;

function secondcoeff(alpha, beta)
    return  alpha[1]*(beta[3] - beta[2]) + 
            alpha[2]*(beta[1] - beta[3]) + 
            alpha[3]*(beta[2] - beta[1]);
end function;

function glueing(E1, E2)
    rootsE1 := E1;
    rootsE2 := E2;

    rhsE1 := &*[ x - i : i in rootsE1];
    rhsE2 := &*[ x - i : i in rootsE2];

    del1 := Discriminant(rhsE1);
    del2 := Discriminant(rhsE2);

    a1 := firstcoeff(rootsE1, rootsE2);
    b1 := firstcoeff(rootsE2, rootsE1);

    a2 := secondcoeff(rootsE1, rootsE2);
    b2 := secondcoeff(rootsE2, rootsE1);

    A := del2 * a1/a2;
    B := del1 * b1/b2;

    alpha1 := rootsE1[1];
    alpha2 := rootsE1[2];
    alpha3 := rootsE1[3];
    beta1 := rootsE2[1];
    beta2 := rootsE2[2];
    beta3 := rootsE2[3];


    h := -1*(
        (A*(alpha2 - alpha1)*(alpha1 - alpha3)*x^2 + B*(beta2 - beta1)*(beta1 - beta3))*
        (A*(alpha3 - alpha2)*(alpha2 - alpha1)*x^2 + B*(beta3 - beta2)*(beta2 - beta1))*
        (A*(alpha1 - alpha3)*(alpha3 - alpha2)*x^2 + B*(beta1 - beta3)*(beta3 - beta2))
    );

    H := HyperellipticCurve(h);

    return H;
end function;

// construct the roots of E^p
alphap := alpha^p;
alphainv := 1/alpha;
alphapinv := 1/alphap;

// construct the curves as arising from the roots
// e.g. E is y^2 = (x - a)(x - b)(x - c)
E := [0, alpha, alphainv];
assert EllipticCurve(&*[x - r : r in E]) eq E_alpha;

Ep := [0, alphap, alphapinv];

// H is the glueing of E x E^(p)
// C_alpha is the (2,2)-isogenous curve to the weil restricition W(E) of E
H := glueing(E, Ep);
C2_alpha := BaseChange(C_alpha, Fp2);

if IsIsomorphic(H, C2_alpha) then
    "Glueing works between E x E^alpha to C_alpha/Fp2";
else
    "Glueing fails but not sure why...";
end if;
