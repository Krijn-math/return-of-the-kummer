// this is an initial version to compute normalisation of a Kummer surface (Section 4)
// this was done very quickly, and can be done much much better
// this takes the most naive approach possible, by simply remapping to all possible permutations of the roots


if assigned is_main_script then
    filename := "file_loader.m";
    Write(filename, "\n" : Overwrite := true);
else
    is_main_script := true;
    print "normalisation.m is being executed directly.";
    filename := "file_loader.m";

    files := [
        "../costello-code/Params.m",
        "../costello-code/Kummer.m",
        "../costello-code/Maps.m",
        "../section2/invariants.m",
        "../section2/more_maps.m",
        "../section2/general.m"
        ];
    Write(filename, "\n" : Overwrite := true);
    for file in files do
        tmp :=  "load '" cat file cat "'; \n"; 
        Write(filename, tmp);
    end for;
end if;
load "file_loader.m";

// load "../section2/general.m";

poly<xx> := PolynomialRing(Fp);

function NonStandardKappa(curve, perm) 
    //assumes six roots for now, permutes the roots according to the permutation given, and then computes the rosenhain
    //invariants that you get by mapping 1 --> infty, 2 -->0 and 3 -->1, so that 4, 5, 6 map to lambda, mu, nu
    //first derives kappa from the assumed mapping, then evaluates mappa on the other roots
    C := curve;
    f := HyperellipticPolynomials(C);
    roots := [ r[1] : r in Roots(f)];

    assert #roots eq 6;

    //permute the roots
    indices := [1, 2, 3, 4, 5, 6]^perm;

    linf := roots[indices[1]];
    l0 := roots[indices[2]];
    l1 := roots[indices[3]];

    //derive the map kappa that will map the roots correctly
    a := l1 - linf;
    b := l0*(linf - l1);
    c := l1 - l0;
    d := linf*(l0 - l1);

    //kappa acts on X by this f function
    ftop := a*xx + b;
    fbot := c*xx + d;

    //evaluate the other roots to get the rosenhain invariants
    lam_top := Evaluate(ftop, roots[indices[4]]);
    lam_bot := Evaluate(fbot, roots[indices[4]]);
    lam := lam_top/lam_bot;

    mu_top := Evaluate(ftop, roots[indices[5]]);
    mu_bot := Evaluate(fbot, roots[indices[5]]);
    mu := mu_top/mu_bot;
    
    nu_top := Evaluate(ftop, roots[indices[6]]);
    nu_bot := Evaluate(fbot, roots[indices[6]]);
    nu := nu_top/nu_bot;

    return [lam, mu, nu];
end function;

function NormalisationCurve(curve)
    //given a curve, computes for every permutation the rosenhain invariants
    //can be optimized much much more by using the many symmetries available

    //also computes the rosenhain invariants for elliptic kummer surfaces
    ROSs := [];
    wellROSs := [];

    IGCs := [];

    for p in Sym(6) do
        ros_p := NonStandardKappa(curve, p);
        Append(~ROSs, ros_p);
        Append(~IGCs, RosenhainToIgusa(ros_p));
        if ros_p[1]*ros_p[2] eq ros_p[3] 
        or ros_p[2]*ros_p[3] eq ros_p[1]
        or ros_p[1]*ros_p[3] eq ros_p[2]
            then
            Append(~wellROSs, ros_p);
        end if;
    end for;

    assert AllEqualIC(IGCs);

    //now we simply find the lexicographically smallest triple lambda, mu, nu
    //there is probably a better Magma function for this, Python will just do it by a single sort on an array of arrays
    sort_wellROSs := SetToSequence({ Sort(r) : r in wellROSs});

    lams := [r[1] : r in sort_wellROSs];
    minlam := Min(lams);

    lams_wellROSs := [r : r in sort_wellROSs | r[1] eq minlam];
    mus := [r[2] : r in lams_wellROSs];
    minmus := Min(mus);

    unique := [r : r in lams_wellROSs | r[2] eq minmus];
    assert #unique eq 1;
    unique := unique[1];

    return unique;
end function;

function ToDegreeSix(ros)
    //out of laziness, was easier to map any curve to a degree six model and then compute the rosenhain variants
    //so this computes a degree six model of a Rosenhain curve by mapping infty to something rational:
    //we make -1 root of cx + d
    a := Random(Fp); a := 0;
    b := Random(Fp); b := 1;
    c := Random(Fp); c := 1;
    d := Random(Fp); d := 1;

    ftop := a*xx + b;
    fbot := c*xx + d;

    roots := [0, 1] cat ros;

    new_roots := [ Fp!Evaluate(ftop, r) / Evaluate(fbot, r) : r in roots];

    Append(~new_roots, Fp!a/c);

    C := HyperellipticCurve(&*[xx - r : r in new_roots]);

    return C;
end function;

function NormaliseRosenhain(ros)
    //maps ros to a normalized set ros
    //for now its dumb: takes the curve C_ros, maps it to some degree 6 model C
    //then computes the possible rosenhains for C and returns the
    //normalized one.

    C := ToDegreeSix(ros);

    return NormalisationCurve(C);
end function;


////////////////////////////////
////////////////////////////////
//////      TESTING      ///////
////////////////////////////////
////////////////////////////////

"WARNING: testing of curve normalisation is slow!";

ROSs := [];
wellROSs := [];

IGCs := [];

//lets first check that permutating these things does give isomorphic curves
for p in Sym(6) do
    ros_p := NonStandardKappa(C_alpha, p);
    Append(~ROSs, ros_p);
    Append(~IGCs, RosenhainToIgusa(ros_p));
    if ros_p[1]*ros_p[2] eq ros_p[3] then
        Append(~wellROSs, ros_p);
    end if;
end for;

assert AllEqualIC(IGCs);

sort_wellROSs := SetToSequence({ Sort(r) : r in wellROSs});

//now lets say our elliptic kummers are derived from E_alpha
//lets take all isomorphic E_A, and compute their associated elliptic Kummers
//then getting the normalized kummer surfaces should match up! this shows that
//we have a unique representant of the isomorphism class
j := jInvariant(E_alpha);
MontAs := jInvToMont(j);

MontAlphas := [ Roots(x^2 + A*x + 1)[1][1] : A in MontAs];

C_alphas := [SupersingularAbelianSurfaceFromMontgomeryCurve(alpha) : alpha in MontAlphas];

Normalisations := [NormalisationCurve(C) : C in C_alphas];
assert #Set(Normalisations) eq 1;

"Curve normalisation works!";
"normalisation.m done";

// here we computed a testset for some rosenhain invariants, which we check against in python
// warning: precomputed for a smaller prime!
if p eq 417942208511 then

    testset := [
        [ 217610473851, 138087012420, 42413722345 ],
        [ 46720581338, 345675709269, 91426010800 ],
        [ 34444146955, 221729241802, 385660306297 ],
        [ 114007141469, 124779713017, 35804802686 ],
        [ 123135305869, 25400171069, 24315095789 ]
    ];

    results := [NormaliseRosenhain(test) : test in testset];

    precomp_results := [
        [ 58594144, 48779918860, 306403563246 ],
        [ 15775240406, 85895158793, 258997075956 ],
        [ 34444146955, 101336964274, 322400069680 ],
        [ 35804802686, 114007141469, 124779713017 ],
        [ 20549989461, 140204151858, 339455135710 ]
    ];

    assert precomp_results eq results;
end if;




