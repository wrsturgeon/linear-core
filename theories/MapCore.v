From Coq Require
  String
  .
From MMaps Require
  MMaps
  .
From LinearCore Require
  OrderedString
  .



Module Map := MMaps.RBT.Make(OrderedString).
Include Map.
