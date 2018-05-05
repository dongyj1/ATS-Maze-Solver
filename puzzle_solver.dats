#include
"share/atspre_staload.hats"
#include
"share/atspre_staload_libats_ML.hats"
#staload
UN = "prelude/SATS/unsafe.sats"


typedef
value = @{n_len=int, f=double, g=double, h=double, from=int}

/**
*   Extern
*/
extern
fun
readPuzzleFromFile(filename: string):$tup(int, int, list0(list0(int)))

extern
fun
print2dMatrix(matrix: list0(list0(int))):void

extern
fun
printValue(i: int, v: value):void

extern
fun
printValueList(l: list0(value)):void

extern
fun
containsTup(list:list0($tup(int, int)), pos:$tup(int, int)):bool

extern
fun
calculate_distance(cur_x:int, cur_y:int, des_x:int, des_y:int):double

extern
fun
list0_contains(l:list0($tup(int, int)), x:$tup(int, int)):bool

/**
*   Math
*/
extern
fun
pow(x:double, y:double): double = "mac#pow"

extern
fun
sqrt(x:double): double = "mac#sqrt"

%{^
#include <math.h>
%}

/**
*   Read Puzzle from text file
*/
implement
readPuzzleFromFile(filename) = 
    let 
        val f = fileref_open_exn(filename, file_mode_r)
        val str_list = (fileref_get_lines_stringlst(f)):list0(string)
        val M = (list0_length(str_list)):int
        // val N = (if M > 0 then list0_length(str_list[0]) else (~1)):int
        val N = (list0_length(string_explode(str_list[0]))):int
        val res = (list0_nil()):list0(list0(int))
        fun
        loop(M:int, N:int, i:int, str_list:list0(string), res:list0(list0(int))):list0(list0(int)) = 
            if i >= M then res
            else
                let
                    val chs = string_explode(str_list[i])
                    val cur = list0_nil()
                    fun loop1(i:int, chs:list0(char), cur:list0(int)):list0(int) = 
                        if i >= list0_length(chs) then cur
                        else
                            let
                                val cur = list0_extend(cur, if chs[i]='1' then 1 else 0)
                            in
                                loop1(i + 1, chs, cur)
                            end
                    val cur = loop1(0, chs, cur)
                    val res = list0_extend(res, cur)
                in
                    loop(M, N, i + 1, str_list, res)
                end
    in
        $tup(M, N, loop(M, N, 0, str_list, res))
    end

/**
*   Print 2d matrix
*/
implement
print2dMatrix(matrix) = 
let
    fun loop(i: int, matrix:list0(list0(int))):void = 
        if i >= list0_length(matrix) then ()
        else
            let
                val () = println!(matrix[i]);
            in
                loop(i + 1, matrix)
            end

in
    loop(0, matrix)
end

/**
*   Print Tuple
*/
fun
printTupList(l:list0($tup(int, int))): void = 
let
    fun loop(i:int):void = 
    if i >= list0_length(l) then ()
    else 
        let
            val () = println!(l[i].0, " ", l[i].1)
        in
            loop(i + 1)
        end
in
    loop(0)
end
/**
*   print value
*/
implement
printValue(i, v) = 
println!(i, " : ", v.n_len, " ", v.f, " ", v.g, " ", v.h, " ", v.from)

/**
*   Print Value list
*/
implement
printValueList(l):void =
let
    fun loop(i:int, l:list0(value)):void = 
        if i >= list0_length(l) then ()
        else
            let
                val () = printValue(i, l[i])
            in
                loop(i + 1, l)
            end
in
    loop(0, l)
end

/**
*   find_lowest_f_score
*/
fun
find_lowest_f_score(M:int, N:int, open_list:list0($tup(int, int)), values:list0(value)):int = 
let
    fun loop(i:int, lowest:double, index:int):int = 
        if i >= list0_length(open_list) then index
        else
            let
                val cur_ind = open_list[i].0 * N + open_list[i].1
                val cur_f = values[cur_ind].f
            in
                if cur_f < lowest then loop(i + 1, cur_f, i)
                else
                    loop(i + 1, lowest, index)
            end

in
    loop(0, 999999.0, 0)
end

fun
isValidNeighbor(matrix:list0(list0(int)), pos:$tup(int, int)):bool = 
let
    
    val m = list0_length(matrix)
    val n = list0_length(matrix[0])
    val x = pos.0
    val y = pos.1
in
    if (x >= 0 andalso x < m andalso y >= 0 andalso y < n andalso let val temp = matrix[x] in temp[y] = 1 end) then true else false
end

/**
*   A* search
*/
fun
ASsearch(des:$tup(int, int), M:int, N:int, matrix:list0(list0(int)),  open_list:list0($tup(int, int)), close_list:list0($tup(int, int)), values:list0(value)):list0(value) = 
// if is_found then values
// else 
    if list0_is_empty(open_list) then 
        let
            val index = des.0 * N + des.1
            val item = values[index]
        in
            list0_fset_at_exn<value>(values, index, 
            @{n_len=item.n_len, f=item.f, g=item.g, h=item.h, from=(~1)}:value)
        end
    else
        let
            val cur_index_open = find_lowest_f_score(M, N, open_list, values):int // index in open_list
            // index in openlist
            val cur_pos = open_list[cur_index_open]
            // val () = println!(cur_pos.0, " ", cur_pos.1)
            val open_list = list0_remove_at_exn(open_list, cur_index_open)
            val close_list = list0_extend(close_list, cur_pos)
        in
            // reach end
            if cur_pos.0 = des.0 andalso cur_pos.1 = des.1 then values
            else
                // if list0_contains(close_list, cur_pos) then ASsearch(des, M, N, matrix, open_list, close_list, values)
                // else
                    let
                        val neighbors = list0_nil()
                        val up = $tup(cur_pos.0 - 1, cur_pos.1)
                        val neighbors = if isValidNeighbor(matrix, up) then list0_extend(neighbors, up) else neighbors
                        val down = $tup(cur_pos.0 + 1, cur_pos.1)
                        val neighbors = if isValidNeighbor(matrix, down) then list0_extend(neighbors, down) else neighbors 
                        val left = $tup(cur_pos.0, cur_pos.1 - 1)
                        val neighbors = if isValidNeighbor(matrix, left) then list0_extend(neighbors, left) else neighbors
                        val right = $tup(cur_pos.0, cur_pos.1 + 1)
                        val neighbors = if isValidNeighbor(matrix, right) then list0_extend(neighbors, right) else neighbors
                        
                        fun
                        it_neighbors(neighbors:list0($tup(int, int)), open_list:list0($tup(int, int)), close_list:list0($tup(int, int)), values:list0(value))
                        :$tup(list0($tup(int, int)), list0($tup(int, int)), list0(value)) = 
                            if list0_is_empty(neighbors) then $tup(open_list, close_list, values)
                            else 
                                let
                                    val neighbor = neighbors[0]:$tup(int, int)
                                    val neighbors = list0_remove_at_exn(neighbors, 0)
                                    
                                in
                                    if list0_contains(close_list, neighbor) then it_neighbors(neighbors, open_list, close_list, values)
                                    else
                                        let
                                            // val () = println!("neighbor: ", neighbor.0, ", ", neighbor.1)
                                            val open_list = if ~list0_contains(open_list, neighbor) then list0_extend(open_list, neighbor) else open_list
                                            val cur_value = values[cur_pos.0 * N + cur_pos.1]
                                            val tentative_gScore = cur_value.g + 1 //calculate_distance(neighbor.0, neighbor.1, cur_pos.0, cur_pos.1)
                                            // val () = println!("tentative_gScore:", tentative_gScore, " ", values[neighbor.0 * N + neighbor.1].g)
                                        in
                                            if tentative_gScore >= values[neighbor.0 * N + neighbor.1].g then it_neighbors(neighbors, open_list, close_list, values)
                                            else
                                                let
                                                    val new_f = tentative_gScore + calculate_distance(neighbor.0, neighbor.1, des.0, des.1)
                                                    val newVal = @{n_len=cur_value.n_len + 1, f=new_f, g=tentative_gScore, h=cur_value.h, from=cur_pos.0 * N + cur_pos.1}:value
                                                    // val () = println!("from", newVal.from)
                                                    val values = list0_fset_at_exn(values, neighbor.0 * N + neighbor.1, newVal)
                                                in
                                                    it_neighbors(neighbors, open_list, close_list, values)
                                                end
                                        end  
                                end
                        val it_neighbors_return = it_neighbors(neighbors, open_list, close_list, values)
                        val open_list = it_neighbors_return.0
                        val close_list = it_neighbors_return.1
                        val values = it_neighbors_return.2
                    in
                        ASsearch(des, M, N, matrix, open_list, close_list, values)
                    end
        end

/**
*   init all h values for the matrix
*/
fun
init_h_value(M: int, N: int, end_pos:$tup(int, int), values:list0(value)): list0(value) = 
let
    val des_row = $UN.cast{double}(end_pos.0)
    val des_col = $UN.cast{double}(end_pos.1)
    fun loop(i: int, M:int, N:int, values:list0(value)): list0(value) = 
    if i >= M * N then values
    else
        let
            val cur_value = values[i]
            val cur_row = i / N
            val cur_col = i % N
            
            val des_row = end_pos.0
            val des_col = end_pos.1
            
            val dist = calculate_distance(cur_row, cur_col, des_row, des_col):double
            // val () = println!(cur_row, " ", cur_col, " ", des_row, " ", des_col, " ", dist)

            val newVal = @{n_len=cur_value.n_len, f=9999999.0, g=9999999.0, h=dist, from=cur_value.from}:value
            val values = list0_fset_at_exn<value>(values, i, newVal)
        in
            loop(i + 1, M, N, values)
        end

in
    loop(0, M, N, values)
end

/**
*   reconstruct route
*/
fun
reconstruct(M:int, N:int, values:list0(value), des:$tup(int, int)):list0($tup(int, int)) = 
let
    val route = list0_make_sing<$tup(int, int)>(des)
    fun
    helper(route:list0($tup(int, int))):list0($tup(int, int)) = 
    let
        val cur = list0_last_exn(route)
        val index = cur.0 * N + cur.1
        val from = values[index].from
        // val () = println!(from)
    in
        if from = (~2) then route else helper(list0_extend(route, $tup(from / N, from % N)))
    end
in
    helper(route)
end

/**
*   Draw route on matrix
*/
fun
draw_route(matrix:list0(list0(int)), route:list0($tup(int, int))):list0(list0(int)) = 
let
    fun
    loop(i:int, matrix:list0(list0(int))) = 
    if i >= list0_length(route) then matrix
    else
        let
            val pos = route[i]
            val row = matrix[pos.0]
            val row = list0_fset_at_exn(row, pos.1, 2)
            val matrix = list0_fset_at_exn(matrix, pos.0, row)
        in
            loop(i + 1, matrix)
        end
in
    loop(0, matrix)
end


/**
*   Utils
*/
implement
containsTup(l, pos) = 
let
    fun loop(l:list0($tup(int, int)), i: int, pos:$tup(int, int)):bool = 
    if i >= list0_length(l) then false
    else 
        if l[i].0 = pos.0 andalso l[i].1 = pos.1 then true
        else loop(l, i + 1, pos)
in  
    loop(l, 0, pos)
end

implement
calculate_distance(cur_row, cur_col, des_row, des_col) = 
let
    val cur_row = $UN.cast{double}(cur_row)
    val cur_col = $UN.cast{double}(cur_col)
    val des_row = $UN.cast{double}(des_row)
    val des_col = $UN.cast{double}(des_col)
in 
    sqrt(pow(des_row - cur_row, 2.0) + pow(des_col - cur_col, 2.0))
end

implement
list0_contains(l, x) = 
let
    fun
    loop(l:list0($tup(int, int)), x:$tup(int, int), i:int) = 
    if i >= list0_length(l) then false
    else
        if l[i].0 = x.0 andalso l[i].1 = x.1 then true else loop(l, x, i + 1)
in
    loop(l, x, 0)
end

implement
main0(argc, argv) = (
    let
        val filename = ("test.txt"):string
        val read_tup = readPuzzleFromFile(filename)
        val M = read_tup.0
        val N = read_tup.1


        val matrix = read_tup.2
        val () = print2dMatrix(matrix)
        

        val open_list = list0_nil()
        val close_list = list0_nil()

        // start & end
        val start_pos = $tup(0, 0)
        val end_pos = $tup(M - 1, N - 1)

        val tempVal = @{n_len=0, f=0.0, g=0.0, h=0.0, from=0}:value

        val values = list0_make_elt<value>(M * N, tempVal)

        val values = init_h_value(M, N, end_pos, values):list0(value)

        // val () = println!(M, N, list0_length(values))

        val start_val = values[start_pos.0 * N + start_pos.1]
        val start_val = @{n_len=0, f=calculate_distance(start_pos.0, start_pos.1, end_pos.0, end_pos.1),
         g=0.0, h=start_val.h, from=(~2)}:value
        val values = list0_fset_at_exn(values, start_pos.0 * N + start_pos.1, start_val)
        val open_list = list0_make_sing<$tup(int, int)>(start_pos)
        val close_list = list0_nil()


        // val () = printValueList(values)
        
        // start A* search
        val values = ASsearch(end_pos, M, N, matrix, open_list, close_list, values)
        // val () = printValueList(values)
        val end_index = end_pos.0 * N + end_pos.1
        val () = println!("Solution : ")
    in
        if values[end_index].from = (~1) then println!("not found!")
            else
                let
                    val () = println!("steps : ", values[end_index].n_len)
                    val route = reconstruct(M, N, values, end_pos)
                    val solved_matrix = draw_route(matrix, route)
                in
                    print2dMatrix(solved_matrix)
                end
    end
)
