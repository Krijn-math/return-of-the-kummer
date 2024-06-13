/*
    This file gives functions that compute several invariants that we use throughout the work,
        such as the j-invariant,
        or deriving the Igusa-Clebsch invariatns from Rosenhian invariants to compare isomorphism classes of Curves/Jacobians
*/

if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "invariants.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";
//load "../costello-code/Kummer.m";

function jInvToMont(j)
    //computes a curve E_A with j(E_A) = j
    _<x> := PolynomialRing(Parent(j));

    top := 256*(x^2 - 3)^3;
    bot := x^2 - 4;
    f := j*bot - top;
    return [ r[1] : r in Roots(f)];
end function;

function MuToRosenhain(mus)
    //given the theta constants, computes the rosenhain invariants of underlying overlying curve
    //makes a choice of sqrt! this is important
    assert mus[3] eq 1;
    assert mus[4] eq 1;
    mu1 := mus[1];
    mu2 := mus[2];
    mu3 := mus[3];
    mu4 := mus[4];

    // Apply the Hadamard map to get the dual constants
    A := mu1 + mu2 + mu3 + mu4;
    B := mu1 + mu2 - mu3 - mu4;
    C := mu1 - mu2 + mu3 - mu4;
    D := mu1 - mu2 - mu3 + mu4;

    assert B eq A - 4;
    assert C eq D;

    tmp := (C*D)/(A*B);
    tmp := Sqrt(tmp);       // this is needed a la 2015/983
    lam := mu1/mu2;
    mu := (1 + tmp)/(1-tmp);
    nu := lam*mu;

    return [lam,mu,nu];
end function;

function MinMuToRosenhain(mus)
    //given the theta constants, computes the rosenhain invariants of the underlying curve

    //this function chooses a different sqrt than the above, which can be seen as mu --> 1/mu
    //and therefore nu --> 1/nu

    assert mus[3] eq 1;
    assert mus[4] eq 1;
    mu1 := mus[1];
    mu2 := mus[2];
    mu3 := mus[3];
    mu4 := mus[4];

    // Apply Hadamard
    A := mu1 + mu2 + mu3 + mu4;
    B := mu1 + mu2 - mu3 - mu4;
    C := mu1 - mu2 + mu3 - mu4;
    D := mu1 - mu2 - mu3 + mu4;

    assert B eq A - 4;
    assert C eq D;

    tmp := (C*D)/(A*B);
    tmp := -Sqrt(tmp);       // choosing a different squareroot

    lam := mu1/mu2;
    mu := (1 + tmp)/(1-tmp);
    nu := lam*mu;

    return [lam,mu,nu];
end function;


function RosenhainToMu(ros)
    // Given rosenhain invariants, computes the theta constants of the K^sqr surface
    lam, mu, nu := Explode(ros);
    mu2 := Sqrt( (mu*(mu - 1)*(lam-nu)) / (nu*(nu-1)*(lam-mu)) );
    mu3 := Sqrt(lam*mu/nu);
    mu4 := 1;
    mu1 := mu2*mu3*nu/mu;
    return [mu1, mu2, mu3, mu4];
end function;

function RosenhainToIgusa(ros)
    // Given Rosenhain invariants, computes Igusa-Clebsch invariants
    _<x> := PolynomialRing(Parent(ros[1]));
    f := x*(x-1)*&*[ x - r : r in ros ];
    return IgusaClebschInvariants(f);
end function;

function EqualIC(IGC)
    // Given list of Igusa Clebsch invariants, computes lambda^2 from the
    // first coordinate, then normalizes the rest, and returns
    s := #IGC;
    lam2 := [IGC[1][1]/IGC[i][1] :  i in [1..s]];
    NormIGC := [ [lam2[i]^j*IGC[i][j] : j in [1..4]] :  i in [1..s]];
    for i in [1..s] do
        NormIGC[i][4] *:= lam2[i];
    end for;

    return NormIGC;
end function;

function AllEqualIC(IGC)
    // Checks that we only get the same projective Igusa-Clebsch invariants
    return #Set(EqualIC(IGC)) eq 1;
end function;

function KummerIsomorphic(K1, K2)
    // Checks if two Kummer surfaces are isomorphic by computing their Igusa-Clebsch invariants
    // from the underlying curve
     igc1 := RosenhainToIgusa(MuToRosenhain(normalise(K1[2])));
     igc2 := RosenhainToIgusa(MuToRosenhain(normalise(K2[2])));
     return AllEqualIC([igc1, igc2]);
end function;

/*
Use the code below to check that our Igusa Clebsch is working 
by mapping to Rosenhain and taking the invariants there
*/


// ros := MuToRosenhain(K[2]);
// igc := RosenhainToIgusa(ros);
// IGC := [igc];
// Append(~IGC, IgusaClebschInvariants(C_alpha));
// assert AllEqualIC(IGC);
// printf "Invariants done\n";
