(* A198683(12) exact Wolfram Language check. *)
(* Created (UTC): 2026-05-20T20:31:16Z *)
(* Repository HEAD: f906a31c0f82f92946a3524ac72e70d392258403 *)

ClearAll[iParens, counts, candidateCounts, expectedThrough11];

iParens[1] = {I};
iParens[n_Integer] := iParens[n] =
  Union[
    Flatten[
      Table[
        Outer[Power, iParens[k], iParens[n - k]],
        {k, n - 1}
      ]
    ],
    SameTest -> Equal
  ];

counts = Table[Length[iParens[n]], {n, 1, 12}];
expectedThrough11 = {1, 1, 2, 3, 7, 15, 34, 77, 187, 462, 1152};

If[
  Take[counts, 11] =!= expectedThrough11,
  Failure[
    "UnexpectedLowerTerms",
    <|
      "Expected" -> expectedThrough11,
      "Observed" -> Take[counts, 11]
    |>
  ],
  candidateCounts =
    Join[
      {1},
      Table[
        Sum[counts[[k]] counts[[n - k]], {k, 1, n - 1}],
        {n, 2, 12}
      ]
    ];

  <|
    "A198683Through12" -> counts,
    "A198683Of12" -> counts[[12]],
    "CandidateCountsFromDistinctLowerSets" -> candidateCounts,
    "CandidatesAt12" -> candidateCounts[[12]],
    "MergedCandidatesAt12" -> candidateCounts[[12]] - counts[[12]]
  |>
]
