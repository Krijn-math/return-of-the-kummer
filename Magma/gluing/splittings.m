if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "splittings.m is being executed directly.";
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
primes := [107
// ,431
];

for p in primes do 

    f2 := Valuation(p+1, 2);


    printf "using prime p := %o - 1\n\n", Factorization(p + 1);
    // printf "prime is %o mod 4\n\n", p mod 4;

    alpha, E_alpha, Fp, Fp2<i>, poly := SupersingularMontgomeryCurve(p);
    C_alpha, J_alpha, beta, gamma, zs := SupersingularAbelianSurfaceFromMontgomeryCurve(alpha);
    K := SupersingularKummerSurfaceFromMontgomeryCurve(alpha);
    PX<X> := PolynomialRing(Fp);
    poly<x>:=PolynomialRing(Fp2);

    r1:=(alpha-1/alpha)^(p-1); r2:=alpha^(p-1); r3:=1/alpha^(p-1);
    betahat:=Sqrt(r3-r2);
    w:=Sqrt((r2-1)^2*(1-r1)*r3);

    //curves/Jacobian defined over Fp2
    Etil_alpha:=EllipticCurve((x-Fp2!r1)*(x-Fp2!r2)*(x-Fp2!r3));
    Ctil_alpha:=HyperellipticCurve((x^2-r1)*(x^2-r2)*(x^2-r3));
    Jtil_alpha:=Jacobian(Ctil_alpha);


    //twists of curves
    A := Coefficients(E_alpha)[2];
    twist_alpha := Roots(x^2 - A*x + 1)[1][1];
    C_twist, J_twist, beta_twist, gamma_twist, zs_twist := SupersingularAbelianSurfaceFromMontgomeryCurve(twist_alpha);
    K_twist := SupersingularKummerSurfaceFromMontgomeryCurve(twist_alpha);


    "Curves initialized\n";


    f_alpha:=poly!HyperellipticPolynomials(C_alpha);
    C_alpha:=HyperellipticCurve(f_alpha);
    J_alpha:=Jacobian(C_alpha);
    "j(E_alpha) = ", jInvariant(E_alpha);

    assert (p+1)*Random(J_alpha) eq J_alpha!0;


    // Splitting isogenies defined over \bar{Fp}
    RI:=RichelotIsogenousSurfaces(J_alpha);
    "Richelot isogenous products of elliptic curves over bar{Fp}:";
    prods := [];
    for S in RI do
        if Type(S) eq SetCart then
            S;
            Append(~prods, S);
        end if;
    end for;
    "";
    // Splitting isogenies defined over Fp
    "Richelot isogenous products of elliptic curves over Fp:";
    C := ChangeRing(C_alpha, Fp);
    // conj for now: L poly of a product is (1+px^2)^2
    L := LPolynomial(C);
    facs := Factorization(L);
    "Lpoly factorises as ", facs;
    "";

    f := facs[1][1];
    R<x> := Parent(f);

    if #facs gt 1 or f ne 1+p*x^2 then 
        "J_alpha is not isogenous to a product of elliptic curves over Fp";
    else 
        "J_alpha is isogenous to a product of elliptic curves over Fp";
    end if;
    "";
    "Finishing with this prime... ";
    "";
    "";
end for;