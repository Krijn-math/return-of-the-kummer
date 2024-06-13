//gives a proof of our improved maps to find u0, u1 and v02

//the grobner basis computation finds 'sol0' and 'sol1' in a nice way
//together with lambda

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "v2_without_grobner.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m",
        "../section2/more_maps.m",
        "../section2/general.m",
        "../section4/biquadratic_general_kummer.m",
        "../section4/biquadratic_intermediate_kummer.m",
        "../section4/point_diff.m",
        "../section3/gaudry_code.m",
        "../section3/fastkummerpairings.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

//load "../section4/point_diff.m";
//load "../section3/fastkummerpairings.m";

w3, w4, w5, w6 := Explode([1] cat ros);
poly<u0,u1,lambda> := PolynomialRing(Fp, 3);

//first generate the embedding maps J --> K
//the mu_i do not appear in here, as they are "corrected" by the CorrectPoint function
f1 := u0*(w3*w5 - u0)*(w4 + w6 + u1);
f2 := u0*(w4*w6 - u0)*(w3 + w5 + u1);
f3 := u0*(w3*w6 - u0)*(w4 + w5 + u1);
f4 := u0*(w4*w5 - u0)*(w3 + w6 + u1);
f := [f1, f2, f3, f4];

D := Random(J_rosenhain);
P := RosenhainToKummer(D, ros, K);
//P := RandomKummerPoint(K);


//scale our point by a random lambda
ala := Random(Fp);
P := [ala*p : p in P];

//the correction function X --> tilde(X) in the paper, we divide out by the mu_i
function CorrectPoint(P, K)
    return [P[i]/K[2][i] : i in [1..4]];
end function;

X := CorrectPoint(P, K);

//all the below should be equal to v0^2
ff := [ f[i] - lambda*X[i] : i in [1..4]];

//thus their diffs are zero
eqs := [ ff[i] - ff[j] : i,j in [1..4] | i lt j];


///////////////////////////////////////////////////////////////
////////                                             //////////
////////           Groebner Approach                 //////////
////////                                             //////////
///////////////////////////////////////////////////////////////

//this is how Groebner does it, and what we try to achieve
GG := GroebnerBasis(eqs); 
lam_sol := Roots(UnivariatePolynomial(GG[3] div lambda))[1][1];
r0 := UnivariatePolynomial(Evaluate(GG[1], <u0, u1, lam_sol>));
r1 := UnivariatePolynomial(Evaluate(GG[2], <u0, u1, lam_sol>));

sol0 := Roots(r0)[1][1];
sol1 := Roots(r1)[1][1];

v02 := Evaluate(ff[1], <sol0, sol1, lam_sol>);
for i in [1..4] do
    assert v02 eq Evaluate(ff[i], <sol0, sol1, lam_sol>);
end for;


///////////////////////////////////////////////////////////////
////////                                             //////////
////////              Linearization approach         //////////
////////                                             //////////
///////////////////////////////////////////////////////////////

//first, try to write it by linearization
function ToMatrix(sysofeqs)
    w, i := Max([#Monomials(f) : f in sysofeqs]);
    monom := Monomials(sysofeqs[i]);
    l := #sysofeqs;
    M := ZeroMatrix(Fp, l, w);

    for i in [1..l] do for j in [1..w] do
        M[i,j] := MonomialCoefficient(sysofeqs[i], monom[j]);
    end for; end for;

    return M;
end function;

M := ToMatrix(eqs);

//the kernel should be one-dimensional, and the solution should be in there
//but the kernel is not aware of our linearilization
kerM := NullspaceOfTranspose(M);
v := Basis(kerM)[1];

//force the linearization to find the vector corresponding to our solution
//where sol = (u0^2, u0*u1, u0, lambda)
f_sol :=  v[1] - x*v[3]^2;
r := Roots(f_sol)[1][1];
sol := r*v;

//check that this is actually the solution
assert 1/ala eq sol[4];
assert Coefficients(D[1])[1] eq sol[3];
assert Coefficients(D[1])[2] eq sol[2]/sol[3];

solv02 := Evaluate(ff[1], <sol[3], sol[2]/sol[3], sol[4]>);
assert solv02 eq v02;
for i in [1..4] do
    assert solv02 eq Evaluate(ff[i], <sol[3], sol[2]/sol[3], sol[4]>);
end for;

original_v0 := (Coefficients(D[2])[1]);
assert original_v0^2 eq solv02;
"linearized formulas WORK";

///////////////////////////////////////////////////////////////
////////                                             //////////
////////           Generalized approach              //////////
////////                                             //////////
///////////////////////////////////////////////////////////////

//we can also write these in terms of variable w3, w4, w5, w6, and then
//given the six equations in eqs, form the matrix M, and compute the row reduced echelon form.
//this gives roughly the same equations as in the Groebner basis computation
//then, take into account that u02 = u0^2 to get lambda

X1, X2, X3, X4 := Explode(X);


u02_fac := -
(w3*w4*w5*X2 - w3*w4*w5*X3 + w3*w4*w6*X1 - w3*w4*w6*X4 - w3*w5*w6*X2 + w3*w5*w6*X4 - w4*w5*w6*X1 + 
    w4*w5*w6*X3)/(w3^2*w4*w5 - w3^2*w4*w6 - w3*w4^2*w5 + w3*w4^2*w6 - w3*w5^2*w6 + w3*w5*w6^2 + w4*w5^2*w6
    - w4*w5*w6^2);
u0u1_fac := -
(-X1 - X2 + X3 + X4)/(w3*w5 - w3*w6 - w4*w5 + w4*w6);
u0_fac := -
(w3*X2 - w3*X4 + w4*X1 - w4*X3 - w5*X2 + w5*X3 - w6*X1 + w6*X4)/(w3^2*w4*w5 - w3^2*w4*w6 - w3*w4^2*w5 + 
    w3*w4^2*w6 - w3*w5^2*w6 + w3*w5*w6^2 + w4*w5^2*w6 - w4*w5*w6^2);


//nicer formulas
num_u0u1_fac := (X1 + X2 - X3 - X4);
denom_u0u1_fac := (w3 - w4)*(w5 - w6);
assert u0u1_fac eq num_u0u1_fac/denom_u0u1_fac;

num_u0_fac := -(w4 - w6)*X1 - (w3 - w5)*X2 + (w4 - w5)*X3 + (w3 - w6)*X4;
denom_u0_fac := (w3 - w4)*(w5 - w6)*(w3*w4 - w5*w6);
assert u0_fac eq num_u0_fac/denom_u0_fac;

num_u02_fac := -
((w3 - w5)*w4*w6*X1 + (w4 - w6)*w3*w5*X2 - (w3 - w6)*w4*w5*X3 - (w4 - w5)*w3*w6*X4);
denom_u02_fac := denom_u0_fac;
assert u02_fac eq num_u02_fac/denom_u02_fac;

lambda_gen := u02_fac/u0_fac^2;
u0_gen := u0_fac * lambda_gen;
u1_gen := u0u1_fac * lambda_gen / u0_gen;
v02_gen := Evaluate(ff[1], <u0_gen, u1_gen, lambda_gen>);

assert u0_gen eq Coefficients(D[1])[1];
assert u1_gen eq Coefficients(D[1])[2];
assert v02_gen eq original_v0^2;

"general formulas WORK";

u0_top := ((w3 - w5)*w4*w6*X1 + (w4 - w6)*w3*w5*X2 - (w3 - w6)*w4*w5*X3 - (w4 - w5)*w3*w6*X4);
u0_bot := (w4 - w6)*X1 + (w3 - w5)*X2 - (w4 - w5)*X3 - (w3 - w6)*X4;
u1_top := -(X1 + X2 - X3 - X4)*(w3*w4 - w5*w6);
u1_bot := u0_bot;

assert u0_gen eq u0_top/u0_bot;
assert u1_gen eq u1_top/u1_bot;

lambda_top := -(w3 - w4)*(w5 - w6)*(w3*w4 - w5*w6)*u0_top;
lambda_bot := u0_bot^2;

assert lambda_gen eq lambda_top/lambda_bot;

"specialized formulas WORK";
"v2_without_grober.m done";