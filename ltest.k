//Linguaggio esercizio 1
/*@ \section{Introduzione}
Questo è un linguaggio di prova contenente i più basilari costrutti del linguaggio imperativo, 
con le caratteristiche elencate successivamente.

\begin{description}

\item [Assegnamento variabili intere e booleane.] Le variabili assegnate sono registrate nello 'state', 
diviso in 'environment' e 'store', nel primo vengono mappate identificatori a locazioni mentre nel secondo
locazioni a valori.

\item [Creazione costrutti condizionali] Le dichiarazioni condizionali gestiscono due casi semantici,
il caso in cui la condizione venga valutata a true o a false. Nella dichiarazione della sintassi di questi
costrutti appare l'attributo strict(1) in modo da valutare solo il primo argomento (la condizione).

\item [Input e output] Sono permesse operazioni di input e output, rispettivamente con l'espressione read(),
con la quale è possibile leggere un numero intero e valutarlo, e l'espressione print(a1,a2,...,an) la qualev
valuta i suoi argomenti e dopo ritorna i suoi valori.

\end{description}
*/

module LTEST-SYNTAX

/*@ \section{Sintassi}
Con il k-framework in questo modulo viene definita la sintassi utilizzata dal linguaggio usando la notazione
BNF (Backus-Naur Form), con l'espressioni terminali incluse fra apici e le non terminali con lettera maiuscola.
In particolare il k-framework estende la notazione BNF con alcuni attributi e notazioni ispirate al SDF (Syntax 
Definition Formalism) più alcuni elementi specifici di K.
Descrizione di alcuni attributi che vengono usati:
- lefteft;
- strict; indica che tutti gli argomenti verranno valutati (in qualsiasi ordine)
- strict(i); indica che verrà valutato solo l'argomento i-esimo
- seqstrict; indica che gli argomenti verranno valutati in ordine sequenziale (sinistra a destra)
- bracket;
- 

*/
	syntax AExp ::= Int | Id 
					| "read" "(" ")"
					> AExp "/" AExp				[strict]
					| AExp "*" AExp				[strict]
					> AExp "+" AExp				[strict]
					| AExp "-" AExp				[strict] 
					| "(" AExp ")" 				[bracket]		
					
	syntax BExp ::= Bool
					| AExp "<=" AExp			[seqstrict]
					| AExp ">=" AExp			[seqstrict]
					| AExp "<" AExp				[seqstrict]
					| AExp ">" AExp				[seqstrict]
					| AExp "==" AExp			[seqstrict]
					| "(" BExp ")" 				[bracket]	
					
	syntax Block ::= "{" "}"
					| "{" Stmts "}"	
					
	syntax Stmt ::= Block
					| "int" Id "=" AExp ";"						[strict(2)]		//superflua basta int Ids ";" (verificare)
					| "bool" Id "=" BExp ";"					[strict(2)]
					| "int" Ids ";"							
					| Id "=" AExp ";"							[strict(2)]
					| Id "=" BExp ";"							[strict(2)]
					| "if" "(" BExp ")" Block "else" Block		[strict(1)]
					| "while" "(" BExp ")" Block				[strict(1)]
					| "print" "(" AExps ")" ";"					[strict]
					| "(" BExp "?" AExp ":" AExp ";)"			[strict(1)]		
											
	syntax AExps ::= List{AExp,","}				[strict]
	syntax Ids ::= List{Id,","}
	syntax Stmts ::= List{Stmt,""}				[seqstrict]
endmodule

module LTEST
	imports LTEST-SYNTAX
	/*@ \subsection{The old IMP constructs}
	K distingue una categoria di termini, chiamata KResult, usata per indicare quali termini sono
	da considerare valori o risultati.
	*/
	syntax KResult ::= Int | Bool 
	
	/*Divido lo stato del programma in un 'environment' e uno 'store'
	 l'environment mapperà i nomi delle variabili alle rispettive locazioni,
	 lo store mapperà locazioni ai valori.*/	
	configuration <T>
					<k>  $PGM:Stmts </k>		//inizializzo la k cell con il programma passato a krun
					<env> .Map </env>
					<store> .Map </store>					
					<stream>
						<in> .List </in>
						<out> .List </out>
					</stream>
				</T>

	
	rule _:Int => .
	rule .AExps => . 		[structural]
	
	//@ \subsubsection{Variable lookup}
	rule <k> X:Id => I:Int ...</k> 
		<env>... X |-> N:Nat ...</env> 
		<store> ... N|-> I ...</store>	  
		
	//@ \subsubsection{Read} 
	rule <k> read() => I:Int ...</k>
		<in> ListItem(I) => .List ...</in>	
		
	//@ \subsubsection{Output} 	
	syntax Printable ::= Int | String
	
	rule <k> print(PExp:Printable,ListExp => ListExp); ...</k>
       <out>... .List => ListItem(PExp) </out>  
	rule print(.AExps); => .  						[structural]
	// rule <k> print (I) ; => I ; ...</k>
		// <out>... .List => ListItem(I:Int) </out>
		
	//@ \subsubsection{Arithmetic construc}  
	rule I1:Int / I2:Int => I1 /Int I2 		when I2 =/=Int 0
	rule I1:Int * I2:Int => I1 *Int I2
	rule I1:Int - I2:Int => I1 -Int I2
	rule I1:Int + I2:Int => I1 +Int I2	  
	
	//@ \subsubsection{Boolean constructs}  
	rule B1:Int <= B2:Int => B1 <=Int B2
	rule B1:Int >= B2:Int => B1 >=Int B2
	rule B1:Int < B2:Int => B1 <Int B2
	rule B1:Int > B2:Int => B1 >Int B2
	rule B1:Int == B2:Int => B1 ==Int B2
	
	/*@ \subsubsection{Block }
	 I blocchi vuoti sono semplicemente ignorati
	 */
	rule {} => . 		
	
	// per i blocchi non vuoti deve essere certo il ripristino dell'ambiente
	// dopo l'esecuzione dei comandi in esso contenuti. In questo modo possiamo definire 
	// variabili locali, dove il loro 'scope' è il block che le contiene
	// rule <k> {S:Stmt} => S ~> env(Rho:Map) ...</k> <env> Rho </env> [structural]
	
	//@ \subsubsection{Composizione sequenziale }
	rule S1:Stmt S2:Stmt  => S1 ~> S2		[structural]
		
	// rules ripristino ambiente
	// rule env(_) ~> env(Rho) => env(Rho) [structural]
	// quando raggiunge env(Rho) sostiuisce l'attuale ambiente con quello vecchio
	// rule <k> env(Rho) => . ...</k> <env> _ => Rho </env> 	[structural]
		  
	// dichiarazione e assegnamento
	rule <k>int X:Id =I:Int ; => I ...</k>
		<env> Env:Map => Env[N/X] </env>					
		<store> N:Int|-> (_ =>I) </store>		 when notBool (X in keys(Env))
		
	rule <k>bool X:Id =B:Bool ; => B ...</k>
		<env> Env:Map => Env[N/X] </env>					
		<store> N:Int|-> (_ =>B) </store>		 when notBool (X in keys(Env))
		
	//dichiarazione di una lista di identificatori
	rule <k> int (X:Id,Xs:Ids => Xs);...</k>
		<env> Env:Map => Env[N/X]</env>
		<store> N:Int |-> (_ => 0) </store>		when notBool (X in keys(Env))
	
	//if/while stmt
	rule if (true) A else _ => A
	rule if (false) _ else A => A
	rule while (B) A => if (B) {A while (B) A} else {} 		[structural]
	rule ((true) ? S : _ ;) => S
	rule ((false) ? _ : S ;) => S
			
endmodule

