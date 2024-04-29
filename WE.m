/* Magma routine associated with the paper "Geometry of the Wiman--Edge monodromy" by Matthew Stover. We refer to this paper below as [WE]. This program can be run at any terminal running Magma by entering "magma WE.m". */

printf "\nThis is a Magma routine associated with the paper\n`Geometry of the Wiman--Edge monodromy' by Matthew Stover.\nWe refer to this paper below as [WE].\n\n";

printf "WARNING: A few computations take a while. Be patient.\n\n";

/* Start by seeing if the reader wants to verify our description of the monodromy subgroup inside SL(2,O). */

printf "Compute the monodromy group as a subgroup of SL(2,O)? (y/n)\n";

read ans0;

if ans0 eq "y" then

  /* Presentation for SL(2,O) */

  G<z, s, m, t, e> := Group<z, s, m, t, e | z^2, (z,s), (z,m), (z,t), (z,e), s^2*z, (s*t)^3, (s*m)^2*z, (t, e), m*t*m^-1=t*e, m*e*m^-1=t*e^2, s*e*s=t*e^-1*s*e^-1*m*z>; 

  printf "\nThe group SL(2,O) will be represented by the group G with generators\nz, s, m, t, e and presentation:\n\n%o\n\n", G;

  printf "The elements z, s, m, t, e represent z_0, sigma, mu, tau, and eta\nfrom [WE], respectively.\n\n";

  /* Define the monodromy subgroup */

  ga := t^-1*e^2;
  gap := s*t^-1*e^2*s^-1;
  gb := t^2*e^-2*s*m^3*e^-2*t^4;
  gbp := e^-2*t^-2*s*m^-3*e^-2;

  H := Rewrite(G, sub<G | ga, gap, gb, gbp>);

  printf "The monodromy group is the subgroup H of G with generators ga, gap,\ngb, gbp (representing gamma_alpha, gamma_alpha', gamma_beta, and\ngamma_beta' from [WE], respectively). As words in G, these are:\n\n%o\n%o\n%o\n%o\n\n", ga, gap, gb, gbp;

  /* Compute the index */

  printf "The index of H in G is:\n%o\n\n", Index(G, H);

  /* Construct the congruence subgroup of level 5 */
  
  printf "We identify SL(2,F5) with the group %o", IdentifyGroup(SL(2,5));
  printf " in the Magma SmallGroups\ndatabase and call it F5. The set of homomorphisms from G to F5 is\ndenoted homs5.\n\n";

  F5 := SmallGroup(120, 5);
  homs5 := Homomorphisms(G, F5);
  printf "There are %o", #homs5;
  printf " homomorphisms from G to F5.\n\nWe define h5 to be the one of them and K5 to be its kernel.\n\n";

  h5 := homs5[1];
  K5 := Rewrite(G, Kernel(h5));

  printf "We check that the second homomorphism has the same kernel: \n%o\n\n", Kernel(homs5[2]) eq K5;

  printf "Uniqueness of K5 implies that it must be SL(2,O)[p5], the congruence\nsubgroup associated with the prime of O with residue field F5.\n\n";

  /* Show that the monodromy group has unipotent image */

  printf "Since the order of h5(H) is %o", #h5(H);
  printf " and since any subgroup of SL(2,F5)\nof order 5 is unipotent, we confirm that the image of H in SL(2,F5)\nis indeed unipotent.\n\n";

  /* Construct the congruence subgroup of level 2 */
  
  printf "We identify SL(2,F4) with the group %o", IdentifyGroup(SL(2,4));
  printf " in the Magma SmallGroups\ndatabase and call it F2. The set of homomorphisms from G to F2 is\ndenoted homs2.\n\n";

  F2 := SmallGroup(60, 5);
  homs2 := Homomorphisms(G, F2);
  printf "There are %o", #homs2;
  printf " homomorphisms from G to F5.\n\nWe define h2 to be a certain one of them and K2 to be its kernel.\n\n";

  good2map := [];
  bad2map := [];
  for j in [1..4] do
    if K5 subset Kernel(homs2[j]) then
      Append(~bad2map, j);
    else
      Append(~good2map, j);
    end if;
  end for;

  h2 := homs2[good2map[1]];
  K2 := Rewrite(G, Kernel(h2));

  printf "We check that another homomorphism has the same kernel: \n%o\n\n", Kernel(homs2[good2map[2]]) eq K2;

  printf "However the other two are different: \n%o\n%o\n\n", Kernel(homs2[bad2map[1]]) eq K2, Kernel(homs2[bad2map[2]]) eq K2;

  printf "We see that the other two contain K5: \n%o\n%o\n\n", K5 subset Kernel(homs2[bad2map[1]]), K5 subset Kernel(homs2[bad2map[2]]);

  printf "This means that the other two are actually the kernels of\nhomomorphisms from H to PSL(2,5), which is isomorphic to\nSL(2,F4). (Our choice of h2 was in fact made using a for\nloop that determines which homomorphisms have kernel containing\nK5. The indices j so that Kernel(homs2[j]) contains K5 are in\na list bad2map and the remaining indices are in a list good2map.)\nThus K2 must be the congruence subgroup SL(2, O)[2] of level 2.\n\n";

  /* Show that the monodromy group has S_3 image */

  printf "The image of H in SL(2,F4) has order %o. ", #h2(H);

  printf "As argued in [WE], this\nimplies that H has image SL(2,F2) < SL(2,F4).\n\n";

  /* Construct the congruence subgroup of level 4 */

  G3840 := LowIndexNormalSubgroups(G, 3840);
  Gindices := [];
  for L in G3840 do Append(~Gindices, Index(G, L`Group)); end for;
  printf "The normal subgroups of SL(2,O) with index at most 3840 are stored\nin G3840 and the index of each group is stored in Gindices. These\nindices are:\n\n%o\n\n", Gindices;

  printf "Since there is a unique normal subgroup of index 3840, it must be the\ncongruence subgroup SL(2,O)[4] of level 4. We call this group K4, and\ndefine a homomorphism to a permutation group F4 representing SL(2,O)/K4.\nThe quotient as a finitely presented group is denoted Q4, and q4 is\na homomorphism from G to Q4. Then f4 is a homomorphism from Q4 to F4\nand h4 is the composite of q4 and f4.\n\n";

  K4 := G3840[#G3840]`Group;
  Q4, q4 := G/K4;
  F4, f4 := PermutationGroup(Q4);
  h4 := q4*f4;

  printf "The group sl(2,F4) < SL(2,R_4) from Lemma 2.2 in [WE] is the image\nof K2 in SL(2,O)/K4, which we denote by sl2F4.\n\n";

  sl2F4 := h4(K2);

  /* Determining the image of H mod 4 */

  HF4 := h4(H);

  printf "We now verify that the image HF4 of H in F4 meets sl(2,F4) in an\nindex two subgroup of sl(2,F4):\n%o\n\n", Index(sl2F4, sl2F4 meet HF4) eq 2;

  printf "We check that m^3 lands in sl(2,F4):\n%o\n\n", h4(m^3) in sl2F4;

  printf "Finally, we check that m^3 is not in the image of H:\n%o\n\n", h4(m^3) in HF4;

  print "This completes our verification that H is the subgroup of G described\nin Theorem 2.4 of [WE].\n\n";

end if;

/* Now see if the reader wants to count cusps. */

printf "Count cusps of X_Gamma? (y/n)\n";

read ans1;

if ans1 eq "y" then

  printf "This will work in PSL(2,O) instead of SL(2,O). All previous\ndefinitions will become irrelevant and/or be overwritten. Okay? (y/n)\n";

  read ans2;

  if ans1 eq "y" then

    /* Presentation for PSL(2,O) */

    G<s, m, t, e> := Group<s, m, t, e | s^2, (s*t)^3, (s*m)^2, (t, e), m*t*m^-1=t*e, m*e*m^-1=t*e^2, s*e*s=t*e^-1*s*e^-1*m>;

    printf "\nThe group PSL(2,O) will be represented by the group G with generators\ns, m, t, e and presentation:\n\n%o\n\n", G;

    printf "The elements s, m, t, e represent the images in PSL(2,O) of sigma,\nmu, tau, and eta from [WE], respectively.\n\n";

    /* Define the monodromy subgroup */

    ga := t^-1*e^2;
    gap := s*t^-1*e^2*s^-1;
    gb := t^2*e^-2*s*m^3*e^-2*t^4;
    gbp := e^-2*t^-2*s*m^-3*e^-2;

    H := Rewrite(G, sub<G | ga, gap, gb, gbp>);

    printf "The monodromy group is the subgroup H of G with generators ga, gap,\ngb, gbp (representing the images in PSL(2,O) of gamma_alpha,\ngamma_alpha', gamma_beta, and gamma_beta' from [WE], respectively).\nAs words in G, these are:\n\n%o\n%o\n%o\n%o\n\n", ga, gap, gb, gbp;

    /* Compute the index */

    printf "The index of H in G is:\n%o\n\n", Index(G, H);

    printf "We will need the congruence subgroup PSL(2, O)[4p5] of level 4p5\nin order to count cusps using covering space theory. We first build\nthe congruence subgroups of level 4 and p5, then take the intersection.\n\n";

    G1920 := LowIndexNormalSubgroups(G, 1920);
    Gindices := [];
    for L in G1920 do Append(~Gindices, Index(G, L`Group)); end for;
    printf "The normal subgroups of PSL(2,O) with index at most 1920 are stored\nin G1920 and the index of each group is stored in Gindices. These\nindices are:\n\n%o\n\n", Gindices;

    printf "Since there is a unique normal subgroup of index 1920, it must be the\ncongruence subgroup PSL(2,O)[4] of level 4. We call this group K4.\n\n";

    K4 := G1920[#G1920]`Group;

    printf "We identify PSL(2,F5) with the group %o", IdentifyGroup(PSL(2,5));
    printf " in the Magma SmallGroups\ndatabase and call it F5. The set of homomorphisms from G to F5 is\ndenoted homs5.\n\n";

    F5 := SmallGroup(60, 5);
    homs5 := Homomorphisms(G, F5);
    printf "There are %o", #homs5;
    printf " homomorphisms from G to F5.\n\nWe define h5 to be a certain one of them and K5 to be its kernel.\n\n";

    good5map := [];
    bad5map := [];
    for j in [1..4] do
      if K4 subset Kernel(homs5[j]) then
        Append(~bad5map, j);
      else
	Append(~good5map, j);
      end if;
    end for;

    h5 := homs5[good5map[1]];
    K5 := Rewrite(G, Kernel(h5));

    printf "We check that another homomorphism has the same kernel: \n%o\n\n", Kernel(homs5[good5map[2]]) eq K5;

    printf "However the other two are different: \n%o\n%o\n\n", Kernel(homs5[bad5map[1]]) eq K5, Kernel(homs5[bad5map[2]]) eq K5;

    printf "We see that the other two contain K4: \n%o\n%o\n\n", K4 subset Kernel(homs5[bad5map[1]]), K4 subset Kernel(homs5[bad5map[2]]);

    printf "This means that the other two are actually the kernels of reduction\nmodulo 2O. (Our choice of h5 was in fact made using a for loop\nthat determines which homomorphisms have kernel containing K4.\nThe indices j so that Kernel(homs5[j]) contains K4 are in\na list bad5map and the remaining indices are in a list good5map.)\nThus K5 must be the congruence subgroup PSL(2, O)[p5] of level p5.\n\n";

    printf "We now define K20 to be the intersection of K4 and K5, which is the\ncongruence subgroup PSL(2, O)[4p5]. Then Q20 is the quotient of G by\nK20, and P20 is a permutation group for this quotient. We have\nhomomorphisms q20 from G to Q20, p20 from Q20 to P20, and r20 from G\nto P20 is the composite. The image of H in P20 is denoted P20H.\n\n";

    K20 := K4 meet K5;
    Q20, q20 := G/K20;
    P20, p20 := PermutationGroup(Q20);
    r20 := q20*p20;
    P20H := r20(H);

    B<M, T, E> := Group<M, T, E | (T, E), M*T*M^-1=T*E, M*E*M^-1=T*E^2>;

    printf "We also need an abstract group isomorphic to the upper-triangular\ncusp group in PSL(2,O). Following Lemma 3.4 in [WE], this is the\ngroup B with generators M, T, E and presentation:\n\n%o\n\n", B;

    printf "We then define a homomorphism b20 from B to P20 by sending M\nto r20(m), etc. Its kernel B20 is abstractly isomorphic to a\ncusp subgroup of K20.\n\n";

    b20 := hom<B->P20 | M->r20(m), T->r20(t), E->r20(e)>;
    P20B := Image(b20);
    B20 := Rewrite(B, Kernel(b20));

    printf "The index of B20 in B is %o. Since P20 has order %o,\nit follows that the manifold associated with PSL(2, O)[4p5]\nhas %o cusps. The image of B in P20 is P20B.\n\n", Index(B, B20), #P20, #P20/Index(B, B20);

    printf "We identify the cusps of PSL(2,O)[4p5] with the set of coset\nrepresentatives of P20B in P20, which we call CuspSet. We then\nuse the action of P20H on these cosets, as described in Prop.\n3.5 of [WE], to create a set CuspOrbits that contains one element\nfor each H-orbit. In other words, CuspOrbits counts the cusps\nof X_Gamma.\n\n";

    CuspSet := RightTransversal(P20, P20B);
    CuspOrbits := [];

    for x in CuspSet do
      found := false;
      for y in CuspOrbits do
        for h in P20H do
          if x*h*y^-1 in P20B then
            found := true;
            break y;
          end if;
        end for;
      end for;
      if found eq false then
        Append(~CuspOrbits, x);
      end if;
    end for;

    printf "We see that X_Gamma has %o cusps.\n\n", #CuspOrbits;

    GCuspOrbits := [];

    for x in CuspOrbits do
      for y in RightTransversal(G, H) do
        for z in P20H do
          if r20(y) eq x*z then
            Append(~GCuspOrbits, y);
            break y;
          end if;
        end for;
      end for;
    end for;

    printf "We also create a set GCuspOrbits consisting of elements of PSL(2,O)\nmapping down to each cusp representative. These elements are:\n\n%o\n\n", GCuspOrbits;

    BCuspSubs := [];

    for x in CuspOrbits do
      newBsub := (P20B^x meet P20H)^(x^-1);
      Append(~BCuspSubs, newBsub);
    end for;

    printf "We then construct a list BCuspSubs consisting of the subgroups\nof P20B associated with images of cusp subgroups of H. Specifically,\nif x is a cusp representative, then the intersection of P20B^x with\nH is the image in P20 of the cusp subgroup of H associated with x.\nWe then conjugate this intersection back to P20B by x^-1 and record\nthe result in BCuspSubs, so these subgroups are all normalized to be\nin P20B, not P20H.\n\n";

    B8gens := [M^-2*E, E^2, T^2];
    BG8gens := [m^-2*e, e^2, t^2];
    B8 := sub<B | B8gens>;
    B24gens := [M^6, T^2, T*E^2];
    BG24gens := [m^6, t^2, t*e^2];
    B24 := sub<B | B24gens>;
    B40gens := [M^2*T^-2*E^-1, T^2*E^6, E^10];
    BG40gens := [m^2*t^-2*e^-1, t^2*e^6, e^10];
    B40 := sub<B | B40gens>;
    B120gens := [M^6, T*E^18, E^20];
    BG120gens := [m^6, t*e^18, e^20];
    B120 := sub<B | B120gens>;

    printf "We now check that the cusp subgroups of H are conjugates of the\ngroups called Lambda_j in Proposition 3.5 of [WE].\n\n";

    printf "The subgroup B120 of B with generators %o\nhas index %o. We check that it contains the kernel of b20:\n\n%o\n\nWe check that b20(B120) is one of the elements of BCuspSubs:\n\n", B120gens, Index(B, B120), B20 subset B120;

    for J in BCuspSubs do
      if Index(P20B, J) eq 120 then
        J eq b20(B120);
      end if;
    end for;

    printf "\nSimilarly, there is a subgroup B40 of B with generators\n%o and index %o.\nAgain, it contains the kernel of b20:\n\n%o\n\nWe check that both b20(B40) and b20(B40^M) are elements of BCuspSubs:\n\n", B40gens, Index(B, B40), B20 subset B40;

    for J in BCuspSubs do
      if Index(P20B, J) eq 40 then
        J eq b20(B40) or J eq b20(B40^M);
      end if;
    end for;

    printf "\nThe subgroup B24 of B with generators %o\nhas index %o, and it contains the kernel of b20:\n\n%o\n\nMoreover, b20(B24) is one of the elements of BCuspSubs:\n\n", B24gens, Index(B, B24), B20 subset B24;

    for J in BCuspSubs do
      if Index(P20B, J) eq 24 then
        J eq b20(B24);
      end if;
    end for;

    printf "\nLastly, the subgroup B8 of B with generators %o\nhas index %o. We again check that it contains the kernel of b20:\n\n%o\n\nThen b20(B8) and b20(B8^T) are in BCuspSubs:\n\n", B8gens, Index(B, B8), B20 subset B8;

    for J in BCuspSubs do
      if Index(P20B, J) eq 8 then
        J eq b20(B8) or J eq b20(B8^T);
      end if;
    end for;

    printf "\nWe also defined BGngens to be elements of G associated with the\ngenerators Bngens for n=8,24,40,120.\n\n";

    printf "We check that the conjugates of generators of B120 by\n%o\nare in H:\n\n", GCuspOrbits[1];

    for x in BG120gens do x^GCuspOrbits[1] in H; end for;

    printf "\nWe check that the conjugates of generators of B24 by\n%o\nare in H:\n\n", GCuspOrbits[2];

    for x in BG24gens do x^GCuspOrbits[2] in H; end for;

    printf "\nWe check that the conjugates of generators of B40 by\n%o\nare in H:\n\n", GCuspOrbits[3];

    for x in BG40gens do x^GCuspOrbits[3] in H; end for;

    printf "\nWe check that the conjugates of generators of B40 by\n%o\nare in H:\n\n", m*GCuspOrbits[4];

    for x in BG40gens do x^(m*GCuspOrbits[4]) in H; end for;

    printf "\nWe check that the conjugates of generators of B8 by\n%o\nare in H:\n\n", t*GCuspOrbits[5];

    for x in BG8gens do x^(t*GCuspOrbits[5]) in H; end for;

    printf "\nWe check that the conjugates of generators of B8 by\n%o\nare in H:\n\n", GCuspOrbits[6];

    for x in BG8gens do x^(GCuspOrbits[6]) in H; end for;

    printf "\nThis completes our analysis of the cusps of X_Gamma.\n\n";

  end if;

end if;
