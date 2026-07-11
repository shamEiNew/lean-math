set_option diagnostics true

instance {α : Type} : HAdd α (List α) (List α) where
  hAdd x xs := x :: xs

#eval HAdd.hAdd 1 [2, 3]

#check @List.map
