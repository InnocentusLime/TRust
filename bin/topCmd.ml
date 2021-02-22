type command =
| Quit
| Reset
| Axiom of string * IrTerm.term
| TcIrTerm of IrTerm.term
| IrDefinition of string * ((string * IrTerm.term) list) * IrTerm.term
| IrPrintDef of string
| IrIsConv of IrTerm.term * IrTerm.term
| IrSimpl of IrTerm.term
| IrLoadModule of string
| Help
