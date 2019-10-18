<<<<<<< HEAD
module ArrayExt = struct
	let exists f arr = 
		let rec impl i f arr =
			if i = Array.length arr then false
			else if f (Array.get arr i) then true
			else impl (i + 1) f arr
		in
		impl 0 f arr

	let existsi f arr = 
		let rec impl i f arr =
			if i = Array.length arr then false
			else if f i (Array.get arr i) then true
			else impl (i + 1) f arr
		in
		impl 0 f arr

	let fold_left_i f init arr =
		let rec impl i acc f arr =
			if i = Array.length arr then acc
			else impl (i + 1) (f i acc (Array.get arr i)) f arr
		in
		impl 0 init f arr

	let fold_right_i f init arr =
		let rec impl i acc f arr =
			if i = -1 then acc
			else impl (i - 1) (f i acc (Array.get arr i)) f arr
		in
		impl (Array.length arr) init f arr 
end

module Aliases = struct
	type 'a str_hashtbl = (string, 'a) Hashtbl.t
	module StrMap = Map.Make(String)
end

=======
module StringMap = Map.Make(String)
>>>>>>> f1ddb288990c4640de608134873338bcddfcd79a
