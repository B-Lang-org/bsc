module Main  where{
import System;
import List;
import Monad;

main::IO(());
main = (do{
  x<-getArgs;
  (case x of {
  ["nothing"]->(return ());
  ["run6"]->run6;
  ["runall"]->runall
});
});
data  Block_element  = If | If_not | Else | Elsif | Endif | S(Int) deriving (Eq,Show);
type Block  = [](Block_element);
block_types::[](Block);
block_types = [[If],[If,Endif],[If,Else],[If,Else,Endif],[If,Elsif],[If,Elsif,Endif],[If,Elsif,Else],[If,Elsif,Else,Endif],[If,Elsif,Elsif],[If,Elsif,Elsif,Endif],[If,Elsif,Elsif,Else],[If,Elsif,Elsif,Else,Endif],[If_not],[If_not,Endif],[If_not,Else],[If_not,Else,Endif],[If_not,Elsif],[If_not,Elsif,Endif],[If_not,Elsif,Else],[If_not,Elsif,Else,Endif],[If_not,Elsif,Elsif],[If_not,Elsif,Elsif,Endif],[If_not,Elsif,Elsif,Else],[If_not,Elsif,Elsif,Else,Endif]];
embeddable_block::Block->Bool;
embeddable_block b = ((==) (last b) Endif);
embeds::[](Block);
embeds = (filter embeddable_block block_types);
try_embed::Block->[](Block);
try_embed b = (do{
  choose_break<-(breaks b);
  e<-embeds;
  (guard (case choose_break of {
  ((_),([]))->(case (embeddable_block b) of {
  (True)->False;
  (_)->True
});
  (_)->True
}));
  (return ((fst choose_break) ++ e ++ (snd choose_break)));
});
breaks::[](a)->[](([](a),[](a)));
breaks x = (tail((zip (inits x) (tails x))));
type Numbered  = (Block_element,Maybe(Int));
process_block_n::Int->Block->[](Numbered);
process_block_n n b = (case b of {
  ([])->[];
  ((:)(Endif) (rest))->((:) ((Endif ),(Nothing )) (process_block_n n rest));
  ((:)(Else) (rest))->((:) ((Else ),(Nothing )) (process_block_n n rest));
  ((:)(S(a)) (rest))->((:) ((S (a )),(Nothing )) (process_block_n n rest));
  ((:)(head) (rest))->((:) ((head ),(Just (n ))) (process_block_n ((+) 1 n) rest))
});
process_block = (process_block_n 1);
to_string_block_element::Numbered->String;
to_string_block_element s = ((case (fst s) of {
  (If)->"`ifdef";
  (If_not)->"`ifndef";
  (Else)->"`else";
  (Elsif)->"`elsif";
  (Endif)->"`endif";
  (S(n))->("placeholder" ++ (show n))
}) ++ (case (snd s) of {
  (Nothing)->"";
  (Just(i))->((++) " def" (show i))
}) ++ "\n");
insert_dummy_placeholders::Block->Block;
insert_dummy_placeholders b = ((:) (S 0) (double_post b (map S (enumFrom 1))));
double_list::a->a->[](a);
double_list x y = [x,y];
double_post::[](a)->[](a)->[](a);
double_post x y = (concat((map (uncurry double_list))((zip x y))));
is_numbered::Block_element->Bool;
is_numbered b = (case b of {
  (Else)->False;
  (Endif)->False;
  (_)->True
});
get_max_number::Block->Int;
get_max_number b = (length (filter is_numbered b));
subsets::[](a)->[]([](a));
subsets x = (case x of {
  ([])->[[]];
  ((:)(head) (tail))->(do{
  s<-(subsets tail);
  [((:) head s),s];
})
});
define_n::Int->String;
define_n n = ("`define def" ++ (show n) ++ "\n");
type Def_token  = Maybe(Int);
data  Statement  = Ifc(Bool)([]((Def_token,[](Statement))))([](Statement)) | Other(Block_element) deriving (Show);
type Rest  = [](Numbered);
type Stmts_Rest  = ([](Statement),Rest);
type Stmt_Rest  = (Statement,Rest);
parse::Rest->[](Statement);
parse l = (case (parse_until_else_or_endif l) of {
  ((s),([]))->s
});
ifdef_chain::Bool->Def_token->Rest->Stmt_Rest;
ifdef_chain is_positive d l = (let {
if_yes = (fst if_yes_calculate);
if_yes_calculate = (parse_until_else_or_endif l);
do_elseif_chain::Rest->([]((Def_token,[](Statement))),Rest);
do_elseif_chain l = (case l of {
  ((:)((Elsif),(d)) (rest1))->(let {
mypart_2 = (parse_until_else_or_endif rest1);
after_mypart = (snd mypart_2);
rest_elseif = (case after_mypart of {
  ((:)((Elsif),(_)) (rest))->(do_elseif_chain after_mypart);
  (_)->([],after_mypart)
})
}
 in (((:) (d,(fst mypart_2)) (fst rest_elseif)),(snd rest_elseif)))
});
if_yes_rest = (snd if_yes_calculate);
elseif_chain_calculate = (case if_yes_rest of {
  ([])->nothing;
  ((:)((Endif),(_)) (_))->([],if_yes_rest);
  ((:)((Else),(_)) (_))->([],if_yes_rest);
  ((:)((Elsif),(_)) (rest))->(do_elseif_chain if_yes_rest)
});
elseif_chain = (fst elseif_chain_calculate);
elseif_chain_rest = (snd elseif_chain_calculate);
elsepart_calculate = (case elseif_chain_rest of {
  ([])->nothing;
  ((:)((Endif),(_)) (rest))->([],rest);
  ((:)((Else),(_)) (rest))->(do_else rest)
});
do_else::Rest->([](Statement),Rest);
do_else l = (parse_until_endif l);
nothing = ([],[]);
elsepart = (fst elsepart_calculate);
rest = (snd elsepart_calculate)
}
 in ((Ifc is_positive ((:) (d,if_yes) elseif_chain) elsepart),rest));
parse_until_else_or_endif::Rest->Stmts_Rest;
parse_until_else_or_endif l = (case l of {
  ([])->([],[]);
  ((:)((Else),(_)) (_))->([],l);
  ((:)((Endif),(_)) (_))->([],l);
  ((:)((Elsif),(_)) (_))->([],l);
  ((:)((S(s)),(_)) (rest))->(let {
more::([](Statement),Rest);
more = (parse_until_else_or_endif rest)
}
 in (((:) (Other (S (s ))) (fst more)),(snd more)));
  ((:)((if_or_not),(tok)) (rest))->(let {
ifdef_result = (ifdef_chain (case if_or_not of {
  (If)->True;
  (If_not)->False
}) tok rest);
until = (parse_until_else_or_endif (snd ifdef_result))
}
 in ((((:) (fst ifdef_result) (fst until)),(snd until))))
});
parse_until_endif::Rest->Stmts_Rest;
parse_until_endif l = (case (parse_until_else_or_endif l) of {
  ((_),((:)((Else),(_)) (_)))->(error "Else unexpected");
  ((s),((:)((Endif),(_)) (rest)))->(s,rest);
  ((s),([]))->(s,[])
});
evaluate_one::Environment->Statement->IO(());
evaluate_one environment f = (case f of {
  (Ifc(positive) (chain) (elsec))->(follow_chain environment positive chain elsec);
  (Other(S(n)))->(do{
  (execute n True);
})
});
evaluate::Environment->[](Statement)->IO(());
evaluate environment l = (mapM_ (evaluate_one environment) l);
type If_branch  = (Def_token,[](Statement));
type If_branches  = [](If_branch);
follow_chain::Environment->Bool->If_branches->[](Statement)->IO(());
follow_chain environment positive l elsec = (case l of {
  ([])->(evaluate environment elsec);
  ((:)((def),(ll)) (rest))->(case ((==) positive (elem def environment)) of {
  (True)->(do{
  (evaluate environment ll);
  (mapM_ mark_ifc_False rest);
  (mark_block_False elsec);
});
  (False)->(do{
  (mark_block_False ll);
  (follow_chain environment True rest elsec);
})
})
});
mark_ifc_False::If_branch->IO(());
mark_ifc_False l = (mark_block_False (snd l));
execute::Int->Bool->IO(());
execute n dir = (putStrLn ("execution " ++ (show n) ++ " " ++ (show dir)));
mark_block_False::[](Statement)->IO(());
mark_block_False s = (mapM_ mark_it_False s);
mark_it_False::Statement->IO(());
mark_it_False s = (case s of {
  (Other(S(n)))->(execute n False);
  (Ifc(_) (chain) (elsec))->(do{
  (mapM_ mark_ifc_False chain);
  (mark_block_False elsec);
})
});
type Environment  = [](Def_token);
perly_output_single::Block->[](Int)->IO(());
perly_output_single b defs = (let {
dummied_block = (process_block(insert_dummy_placeholders(b)))
}
 in (do{
  ((mapM_ putStr)((map define_n)(defs)));
  (putStr((concatMap to_string_block_element)(dummied_block)));
  ((evaluate (map Just defs))(parse(dummied_block)));
  (putStrLn "====");
}));
perly_many_defs::Block->IO(());
perly_many_defs b = (mapM_ (perly_output_single b) (subsets (enumFromTo 1 (get_max_number b))));
run6::IO(());
run6 = (perly_many_defs ((!!) block_types 6));
runall::IO(());
runall = (mapM_ perly_many_defs ((++) embeds (concatMap try_embed embeds)))
}

