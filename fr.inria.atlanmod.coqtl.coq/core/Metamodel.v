(** * Metamodel Class **)
Require Export core.Typing.
Require Export core.Decidability.
Require Export core.Object.

Class Metamodel 
  (ModelElement: Type) (ModelLink: Type) 
  (ModelClass: Type) (ModelReference: Type) 
`{Typing_Elem: Typing ModelElement ModelClass} `{Typing_Link : Typing ModelLink ModelReference}
`{Decidability ModelClass} `{Decidability ModelReference}
`{Object ModelElement} := {

getTyping_Elem := Typing_Elem;
getTyping_Link := Typing_Link;
getModelLink := ModelLink;
}.

