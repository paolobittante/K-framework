//Linguaggio esercizio 1

module IMP-SYNTAX
	syntax Exp1 ::= Int | Id
					| "read" "(" ")"
					> Exp1 "/" Exp1				[left,strict,division]
					| Exp1 "*" Exp1				[left,strict]
					> Exp1 "+" Exp1				[left,strict]
					| Exp1 "-" Exp1				[left,strict]
					> Id "=" Exp1				[strict(2)]
					| Id "=" Exp2				[strict(2)]
					| "(" Exp1 ")" 				[bracket]					
	syntax Exp2 ::= Bool
					| Exp1 "<=" Exp1			[seqstrict]					
					| "(" Exp2 ")" 				[bracket]					
	syntax Block ::= "{" "}"
					| "{" Stmts "}"	
	syntax Stmt ::= Block
					| Exp1 ";"
					| "if" "(" Exp2 ")" Block "else" Block		[strict(1)]
					| "while" "(" Exp2 ")" Block				[strict(1)]
					| "print" "(" Exp1s ")" ";"					[strict]
					| Exp2 "?" Exp1 ":" Exp1					[strict(1)]		

	syntax Exp1s ::= List{Exp1,","}
	syntax Stms ::= List{Stmt,""}
endmodule

module IMP
	imports IMP-SYNTAX	
	syntax KResult ::= Int | Bool 
	
	configuration <T>
					<k>  $PGM:Stmts </k>		//inizializzo la k cell con il programma passato a krun
					<env> .Map </env>
					<store> .Map </store>
					<stream>
					<in> .List </in>
					<out> .List </out>
					</stream>
				</T>

	
	rule <k> S:Id => I:Int ...</k> <env>... S |-> N ...</env> <store> ... N|-> I ...</store>	//lookup rule ???  
	rule <k> S:Id => I:Bool ...</k> <env>... S |-> N ...</env> <store> ... N|-> I ...</store>
	
	rule <k> read() => I </k>
		<in> ListItem(I:Int) => .List ...</in>		[read]
		
//Exp1	  
	rule I1 / I2 => I1 /Int I2 		when I2 =/=Int 0
	rule I1 * I2 => I1 *Int I2
	rule I1 - I2 => I1 -Int I2
	rule I1 + I2 => I1 +Int I2
	  

//Exp2
	rule B1 <= B2 => B1 <=Int B2

//Block
	//rule <k> {}
	
	/*assegnamento
	rule <k> int (X,Xs => Xs); ... </k>			
		<env> Rho:Map => Rho[N/X] </env>			controllare che x non esista già
		<store>... .Map => N|->0 ...</store>
	  when fresh(N:Nat)
	  */
	  
	rule <k> X =I:Int => I ...</k>
		<env>... X|-> N ...</env>
		<store>... N|-> (_ =>I) ...</store>		 //_ variabile anonima	  
endmodule