'''This project was mediated through Sheila McIlraith and is not 
to be copy and used for educational purposes which can lead to Academic Integrity'''


#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  

'''
Construct and return Tenner Grid CSP models.
'''

from cspbase import *
import itertools

def tenner_csp_model_1(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along 
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner grid using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from 
       (0,0) to (n,9)) where n can be 3 to 8.
       
       
       The input board is specified as a pair (n_grid, last_row). 
       The first element in the pair is a list of n length-10 lists.
       Each of the n lists represents a row of the grid. 
       If a -1 is in the list it represents an empty cell. 
       Otherwise if a number between 0--9 is in the list then this represents a 
       pre-set board position. E.g., the board
    
       ---------------------  
       |6| |1|5|7| | | |3| |
       | |9|7| | |2|1| | | |
       | | | | | |0| | | |1|
       | |9| |0|7| |3|5|4| |
       |6| | |5| |0| | | | |
       ---------------------
       would be represented by the list of lists
       
       [[6, -1, 1, 5, 7, -1, -1, -1, 3, -1],
        [-1, 9, 7, -1, -1, 2, 1, -1, -1, -1],
        [-1, -1, -1, -1, -1, 0, -1, -1, -1, 1],
        [-1, 9, -1, 0, 7, -1, 3, 5, 4, -1],
        [6, -1, -1, 5, -1, 0, -1, -1, -1,-1]]
       
       
       This routine returns model_1 which consists of a variable for
       each cell of the board, with domain equal to {0-9} if the board
       has a -1 at that position, and domain equal {i} if the board has
       a fixed number i at that cell.
       
       model_1 contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.).
       model_1 also constains n-nary constraints of sum constraints for each 
       column.
    '''
    #initiliaze the tenner_csp
    tenner_csp = CSP('tenner_csp')
    
    #We first initialize n_grid and last_row
    n_grid = initial_tenner_board[0]
    last_row = initial_tenner_board[1]
    domain = [0,1,2,3,4,5,6,7,8,9]
    variable_array = []
    
    #Initialize the varaible_array list
    for i in range(0,len(n_grid)):
        variable_array.append([])
    
    #We assign all domain values to the variables_array[i][j] cell elements 
    for i in range(0,len(n_grid)):
        for j in range(0,10):
            if n_grid[i][j] != -1:
                variable_array[i].append(Variable('cell'+str(i)+str(j),[n_grid[i][j]]))
                tenner_csp.add_var(variable_array[i][j])
            else:
                variable_array[i].append(Variable('cell'+str(i)+str(j),domain))
                tenner_csp.add_var(variable_array[i][j])
    
    #Binary-Not-Equal constraint
    #c = Constraint('name',satisfying varibles)
    #Make seperate case if two values are -1 and -1
    spec_satis_tup = []
    for i in range(0,len(domain)):
        for j in range(0,len(domain)):
            if i != j:
                spec_satis_tup.append([domain[i],domain[j]])
    
    #build the row constraints 
    for i in range(0,len(n_grid)):
        for j in range(0,10):
            k = 10-(j+1)
            satis_tup = []
            while k > 0:
                c = Constraint('C',[variable_array[i][j],variable_array[i][-1*(k-10)]])
                #print(-1*(k-10))
                if n_grid[i][j] == -1:
                    if n_grid[i][-1*(k-10)] == -1:
                        c.add_satisfying_tuples(spec_satis_tup)
                    elif n_grid[i][-1*(k-10)] != -1:
                        for v in range(0,len(domain)):
                            if domain[v] != n_grid[i][-1*(k-10)]:
                                satis_tup.append([domain[v],n_grid[i][-1*(k-10)]])
                        c.add_satisfying_tuples(satis_tup)
            
                elif n_grid[i][j] != -1:
                    if n_grid[i][-1*(k-10)] == -1:
                        for v in range(0,len(domain)):
                            if n_grid[i][j] != domain[v]:
                                satis_tup.append([n_grid[i][j],domain[v]])
                        c.add_satisfying_tuples(satis_tup)
                    elif n_grid[i][-1*(k-10)] != -1:
                        c.add_satisfying_tuples([[n_grid[i][j],n_grid[i][-1*(k-10)]]])
               
                k = k-1
                    
                tenner_csp.add_constraint(c)
    
    #build the bottom row constraints using Binary Constraint
    #edge cases:
    #make a list of just the edge values of j
    edge_index = [0,9]
    for i in range(0,len(n_grid)-1):
        for j in range(0,len(edge_index)):
            #we check for edge cases. The leftmost edge and the rightmost edge
            if j == 0:
                for v in range(0,2):
                    satis_tup = []
                    if v == 0:
                        #bottom element
                        #check condition when it is -1 
                        c = Constraint('C',[variable_array[i][edge_index[j]],variable_array[i+1][edge_index[j]]])
                        if n_grid[i][edge_index[j]] == -1:
                            if n_grid[i+1][edge_index[j]] == -1:
                                c.add_satisfying_tuples(spec_satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]] != -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i+1][edge_index[j]] != domain[v2]:
                                        satis_tup.append([domain[v2],n_grid[i+1][edge_index[j]]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                        elif n_grid[i][edge_index[j]] != -1:
                            if n_grid[i+1][edge_index[j]] == -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i][edge_index[j]] != domain[v2]:
                                        satis_tup.append([n_grid[i][edge_index[j]],domain[v2]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]] != -1:
                                c.add_satisfying_tuples([[n_grid[i][edge_index[j]],n_grid[i+1][edge_index[j]]]])
                                tenner_csp.add_constraint(c)  
                           
                    elif v == 1:
                        #bottom right element 
                        #check when element is -1
                        c = Constraint('C',[variable_array[i][edge_index[j]],variable_array[i+1][edge_index[j]+1]])
                        if n_grid[i][edge_index[j]] == -1:
                            if n_grid[i+1][edge_index[j]+1] == -1:
                                c.add_satisfying_tuples(spec_satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]+1] != -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i+1][edge_index[j]+1] != domain[v2]:
                                        satis_tup.append([domain[v2],n_grid[i+1][edge_index[j]+1]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                        #check when element is not -1
                        elif n_grid[i][edge_index[j]] != -1:
                            if n_grid[i+1][edge_index[j]+1] == -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i][edge_index[j]] != domain[v2]:
                                        satis_tup.append([n_grid[i][edge_index[j]],domain[v2]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]+1] != -1:
                                c.add_satisfying_tuples([[n_grid[i][edge_index[j]],n_grid[i+1][edge_index[j]+1]]])
                                tenner_csp.add_constraint(c)                                
                                
            elif j == 1:
                for v in range(0,2):
                    satis_tup = []
                    if v == 0:
                        #bottom element
                        #check condition when it is -1 
                        c = Constraint('C',[variable_array[i][edge_index[j]],variable_array[i+1][edge_index[j]]])
                        if n_grid[i][edge_index[j]] == -1:
                            if n_grid[i+1][edge_index[j]] == -1:
                                c.add_satisfying_tuples(spec_satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]] != -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i+1][edge_index[j]] != domain[v2]:
                                        satis_tup.append([domain[v2],n_grid[i+1][edge_index[j]]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                        elif n_grid[i][edge_index[j]] != -1:
                            if n_grid[i+1][edge_index[j]] == -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i][edge_index[j]] != domain[v2]:
                                        satis_tup.append([n_grid[i][edge_index[j]],domain[v2]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]] != -1:
                                c.add_satisfying_tuples([[n_grid[i][edge_index[j]],n_grid[i+1][edge_index[j]]]])
                                tenner_csp.add_constraint(c)     
            
                    elif v == 1:
                        #bottom left element
                        c = Constraint('C',[variable_array[i][edge_index[j]], variable_array[i+1][edge_index[j]-1]])
                        if n_grid[i][edge_index[j]] == -1:
                            if n_grid[i+1][edge_index[j]-1] == -1:
                                c.add_satisfying_tuples(spec_satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]-1] != -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i+1][edge_index[j]-1] != domain[v2]:
                                        satis_tup.append([domain[v2],n_grid[i+1][edge_index[j]-1]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                        elif n_grid[i][edge_index[j]] != -1:
                            if n_grid[i+1][edge_index[j]-1] == -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i][edge_index[j]] != domain[v2]:
                                        satis_tup.append([n_grid[i][edge_index[j]],domain[v2]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]-1] != -1:
                                c.add_satisfying_tuples([[n_grid[i][edge_index[j]],n_grid[i+1][edge_index[j]-1]]])
                                tenner_csp.add_constraint(c)
            else:
                pass 
                                    
    for i in range(0,len(n_grid)-1):
        for j in range(1,9):
            for v in range(0,3):
                satis_tup = []
                if v == 0:
                    #bottom element
                    #check condition when it is -1 
                    c = Constraint('C',[variable_array[i][j],variable_array[i+1][j]])
                    if n_grid[i][j] == -1:
                        if n_grid[i+1][j] == -1:
                            c.add_satisfying_tuples(spec_satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j] != -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i+1][j] != domain[v2]:
                                    satis_tup.append([domain[v2],n_grid[i+1][j]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                        
                    #check condition when is is not -1
                    elif n_grid[i][j] != -1:
                        if n_grid[i+1][j] == -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i][j] != domain[v2]:
                                    satis_tup.append([n_grid[i][j],domain[v2]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j] != -1:
                            c.add_satisfying_tuples([[n_grid[i][j],n_grid[i+1][j]]])
                            tenner_csp.add_constraint(c)                   
    
                elif v == 1:
                    #bottom right element 
                    #check when element is -1
                    c = Constraint('C',[variable_array[i][j],variable_array[i+1][j+1]])
                    if n_grid[i][j] == -1:
                        if n_grid[i+1][j+1] == -1:
                            c.add_satisfying_tuples(spec_satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j+1] != -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i+1][j+1] != domain[v2]:
                                    satis_tup.append([domain[v2],n_grid[i+1][j+1]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                    #check when element is not -1
                    elif n_grid[i][j] != -1:
                        if n_grid[i+1][j+1] == -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i][j] != domain[v2]:
                                    satis_tup.append([n_grid[i][j],domain[v2]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j+1] != -1:
                            c.add_satisfying_tuples([[n_grid[i][j],n_grid[i+1][j+1]]])
                            tenner_csp.add_constraint(c)
            
                    
                elif v == 2:
                    #bottom left element
                    c = Constraint('C',[variable_array[i][j], variable_array[i+1][j-1]])
                    if n_grid[i][j] == -1:
                        if n_grid[i+1][j-1] == -1:
                            c.add_satisfying_tuples(spec_satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j-1] != -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i+1][j-1] != domain[v2]:
                                    satis_tup.append([domain[v2],n_grid[i+1][j-1]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                    elif n_grid[i][j] != -1:
                        if n_grid[i+1][j-1] == -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i][j] != domain[v2]:
                                    satis_tup.append([n_grid[i][j],domain[v2]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j-1] != -1:
                            c.add_satisfying_tuples([[n_grid[i][j],n_grid[i+1][j-1]]])
                            tenner_csp.add_constraint(c)
    
    #build the sum constraint n-ary constraints of sum constraint
    #last row = intial_tenner_board[1] already itilialized
    for i in range(0,10):
        #store all values to array
        array = []
        array_sum = []
        var_array = []
        for j in range(0,len(n_grid)):
            if n_grid[j][i] != -1:
                array.append([n_grid[j][i]])
                var_array.append(variable_array[j][i])
            elif n_grid[j][i] == -1:
                array.append(domain)
                var_array.append(variable_array[j][i])
            else:
                pass
        #print(array)
        #At this stage we created a list of lists: eg) [[2],[0,1,2,3,4,5,6,7,8,9],[3],...]
        #We now want to permute all possible combinations belonging to the variables 
        c = Constraint('C',var_array)
        array_new = list(itertools.product(*array))
        for k in range(0,len(array_new)):
            if sum(array_new[k]) == last_row[i]:
                array_sum.append(array_new[k])
            else:
                pass 
        c.add_satisfying_tuples(array_sum)
        tenner_csp.add_constraint(c)
     
    return tenner_csp,variable_array

#IMPLEMENT

##############################

def tenner_csp_model_2(initial_tenner_board):
    '''Return a CSP object representing a Tenner Grid CSP problem along 
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from 
       (0,0) to (n,9)) where n can be 3 to 8.

       The input board takes the same input format (a list of n length-10 lists
       specifying the board as tenner_csp_model_1.
    
       The variables of model_2 are the same as for model_1: a variable
       for each cell of the board, with domain equal to {0-9} if the
       board has a -1 at that position, and domain equal {i} if the board
       has a fixed number i at that cell.

       However, model_2 has different constraints. In particular,
       model_2 has a combination of n-nary 
       all-different constraints and binary not-equal constraints: all-different 
       constraints for the variables in each row, binary constraints for  
       contiguous cells (including diagonally contiguous cells), and n-nary sum 
       constraints for each column. 
       Each n-ary all-different constraint has more than two variables (some of 
       these variables will have a single value in their domain). 
       model_2 should create these all-different constraints between the relevant 
       variables.
    '''

    #initiliaze the tenner_csp
    tenner_csp = CSP('tenner_csp')
    
    #We first initialize n_grid and last_row
    n_grid = initial_tenner_board[0]
    last_row = initial_tenner_board[1]
    domain = [0,1,2,3,4,5,6,7,8,9]
    variable_array = []
    
    #Initialize the varaible_array list
    for i in range(0,len(n_grid)):
        variable_array.append([])
    
    #We assign all domain values to the variables_array[i][j] cell elements 
    for i in range(0,len(n_grid)):
        for j in range(0,10):
            if n_grid[i][j] != -1:
                variable_array[i].append(Variable('cell'+str(i)+str(j),[n_grid[i][j]]))
                tenner_csp.add_var(variable_array[i][j])
            else:
                variable_array[i].append(Variable('cell'+str(i)+str(j),domain))
                tenner_csp.add_var(variable_array[i][j])
    
    #Binary-Not-Equal constraint
    #c = Constraint('name',satisfying varibles)
    #Make seperate case if two values are -1 and -1
    spec_satis_tup = []
    for i in range(0,len(domain)):
        for j in range(0,len(domain)):
            if i != j:
                spec_satis_tup.append([domain[i],domain[j]])
    
    #build the row constraints using n-ary all different constraints
    #satis_tup_nary = list(itertools.permutations(range(10),10))
    for i in range(0,len(n_grid)):
        var_array = []
        var_ref = []
        domain_nary = [0,1,2,3,4,5,6,7,8,9]
        domain_val = []
        for j in range(0,len(n_grid[i])):
           if n_grid[i][j] != -1:
               domain_val.append(n_grid[i][j])
        domain_nary = [x for x in domain_nary if x not in domain_val]
        
        for j in range(0,10):
           var_array.append(variable_array[i][j]) 
           if n_grid[i][j] == -1:
               var_ref.append(domain_nary)
           elif n_grid[i][j] != -1:
               var_ref.append([n_grid[i][j]])
       
        satis_tup_nary = [x for x in itertools.product(*var_ref) if len(x) == len(set(x))]
        c = Constraint('C',var_array)
        c.add_satisfying_tuples(satis_tup_nary)
        tenner_csp.add_constraint(c)
        
       
            
    #build the bottom row constraints using Binary Constraint
    #edge cases:
    #make a list of just the edge values of j
    edge_index = [0,9]
    for i in range(0,len(n_grid)-1):
        for j in range(0,len(edge_index)):
            #we check for edge cases. The leftmost edge and the rightmost edge
            if j == 0:
                for v in range(0,2):
                    satis_tup = []
                    if v == 0:
                        #bottom element
                        #check condition when it is -1 
                        c = Constraint('C',[variable_array[i][edge_index[j]],variable_array[i+1][edge_index[j]]])
                        if n_grid[i][edge_index[j]] == -1:
                            if n_grid[i+1][edge_index[j]] == -1:
                                c.add_satisfying_tuples(spec_satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]] != -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i+1][edge_index[j]] != domain[v2]:
                                        satis_tup.append([domain[v2],n_grid[i+1][edge_index[j]]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                        elif n_grid[i][edge_index[j]] != -1:
                            if n_grid[i+1][edge_index[j]] == -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i][edge_index[j]] != domain[v2]:
                                        satis_tup.append([n_grid[i][edge_index[j]],domain[v2]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]] != -1:
                                c.add_satisfying_tuples([[n_grid[i][edge_index[j]],n_grid[i+1][edge_index[j]]]])
                                tenner_csp.add_constraint(c)  
                           
                    elif v == 1:
                        #bottom right element 
                        #check when element is -1
                        c = Constraint('C',[variable_array[i][edge_index[j]],variable_array[i+1][edge_index[j]+1]])
                        if n_grid[i][edge_index[j]] == -1:
                            if n_grid[i+1][edge_index[j]+1] == -1:
                                c.add_satisfying_tuples(spec_satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]+1] != -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i+1][edge_index[j]+1] != domain[v2]:
                                        satis_tup.append([domain[v2],n_grid[i+1][edge_index[j]+1]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                        #check when element is not -1
                        elif n_grid[i][edge_index[j]] != -1:
                            if n_grid[i+1][edge_index[j]+1] == -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i][edge_index[j]] != domain[v2]:
                                        satis_tup.append([n_grid[i][edge_index[j]],domain[v2]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]+1] != -1:
                                c.add_satisfying_tuples([[n_grid[i][edge_index[j]],n_grid[i+1][edge_index[j]+1]]])
                                tenner_csp.add_constraint(c)                                
                                
            elif j == 1:
                for v in range(0,2):
                    satis_tup = []
                    if v == 0:
                        #bottom element
                        #check condition when it is -1 
                        c = Constraint('C',[variable_array[i][edge_index[j]],variable_array[i+1][edge_index[j]]])
                        if n_grid[i][edge_index[j]] == -1:
                            if n_grid[i+1][edge_index[j]] == -1:
                                c.add_satisfying_tuples(spec_satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]] != -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i+1][edge_index[j]] != domain[v2]:
                                        satis_tup.append([domain[v2],n_grid[i+1][edge_index[j]]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                        elif n_grid[i][edge_index[j]] != -1:
                            if n_grid[i+1][edge_index[j]] == -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i][edge_index[j]] != domain[v2]:
                                        satis_tup.append([n_grid[i][edge_index[j]],domain[v2]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]] != -1:
                                c.add_satisfying_tuples([[n_grid[i][edge_index[j]],n_grid[i+1][edge_index[j]]]])
                                tenner_csp.add_constraint(c)     
            
                    elif v == 1:
                        #bottom left element
                        c = Constraint('C',[variable_array[i][edge_index[j]], variable_array[i+1][edge_index[j]-1]])
                        if n_grid[i][edge_index[j]] == -1:
                            if n_grid[i+1][edge_index[j]-1] == -1:
                                c.add_satisfying_tuples(spec_satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]-1] != -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i+1][edge_index[j]-1] != domain[v2]:
                                        satis_tup.append([domain[v2],n_grid[i+1][edge_index[j]-1]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                        elif n_grid[i][edge_index[j]] != -1:
                            if n_grid[i+1][edge_index[j]-1] == -1:
                                for v2 in range(0,len(domain)):
                                    if n_grid[i][edge_index[j]] != domain[v2]:
                                        satis_tup.append([n_grid[i][edge_index[j]],domain[v2]])
                                c.add_satisfying_tuples(satis_tup)
                                tenner_csp.add_constraint(c)
                            elif n_grid[i+1][edge_index[j]-1] != -1:
                                c.add_satisfying_tuples([[n_grid[i][edge_index[j]],n_grid[i+1][edge_index[j]-1]]])
                                tenner_csp.add_constraint(c)
            else:
                pass 
                                    
    for i in range(0,len(n_grid)-1):
        for j in range(1,9):
            for v in range(0,3):
                satis_tup = []
                if v == 0:
                    #bottom element
                    #check condition when it is -1 
                    c = Constraint('C',[variable_array[i][j],variable_array[i+1][j]])
                    if n_grid[i][j] == -1:
                        if n_grid[i+1][j] == -1:
                            c.add_satisfying_tuples(spec_satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j] != -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i+1][j] != domain[v2]:
                                    satis_tup.append([domain[v2],n_grid[i+1][j]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                        
                    #check condition when is is not -1
                    elif n_grid[i][j] != -1:
                        if n_grid[i+1][j] == -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i][j] != domain[v2]:
                                    satis_tup.append([n_grid[i][j],domain[v2]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j] != -1:
                            c.add_satisfying_tuples([[n_grid[i][j],n_grid[i+1][j]]])
                            tenner_csp.add_constraint(c)                   
    
                elif v == 1:
                    #bottom right element 
                    #check when element is -1
                    c = Constraint('C',[variable_array[i][j],variable_array[i+1][j+1]])
                    if n_grid[i][j] == -1:
                        if n_grid[i+1][j+1] == -1:
                            c.add_satisfying_tuples(spec_satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j+1] != -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i+1][j+1] != domain[v2]:
                                    satis_tup.append([domain[v2],n_grid[i+1][j+1]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                    #check when element is not -1
                    elif n_grid[i][j] != -1:
                        if n_grid[i+1][j+1] == -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i][j] != domain[v2]:
                                    satis_tup.append([n_grid[i][j],domain[v2]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j+1] != -1:
                            c.add_satisfying_tuples([[n_grid[i][j],n_grid[i+1][j+1]]])
                            tenner_csp.add_constraint(c)
            
                    
                elif v == 2:
                    #bottom left element
                    c = Constraint('C',[variable_array[i][j], variable_array[i+1][j-1]])
                    if n_grid[i][j] == -1:
                        if n_grid[i+1][j-1] == -1:
                            c.add_satisfying_tuples(spec_satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j-1] != -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i+1][j-1] != domain[v2]:
                                    satis_tup.append([domain[v2],n_grid[i+1][j-1]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                    elif n_grid[i][j] != -1:
                        if n_grid[i+1][j-1] == -1:
                            for v2 in range(0,len(domain)):
                                if n_grid[i][j] != domain[v2]:
                                    satis_tup.append([n_grid[i][j],domain[v2]])
                            c.add_satisfying_tuples(satis_tup)
                            tenner_csp.add_constraint(c)
                        elif n_grid[i+1][j-1] != -1:
                            c.add_satisfying_tuples([[n_grid[i][j],n_grid[i+1][j-1]]])
                            tenner_csp.add_constraint(c)
    
    #build the sum constraint n-ary constraints of sum constraint
    #last row = intial_tenner_board[1] already itilialized
    for i in range(0,10):
        #store all values to array
        array = []
        array_sum = []
        var_array = []
        for j in range(0,len(n_grid)):
            if n_grid[j][i] != -1:
                array.append([n_grid[j][i]])
                var_array.append(variable_array[j][i])
            elif n_grid[j][i] == -1:
                array.append(domain)
                var_array.append(variable_array[j][i])
            else:
                pass
        #print(array)
        #At this stage we created a list of lists: eg) [[2],[0,1,2,3,4,5,6,7,8,9],[3],...]
        #We now want to permute all possible combinations belonging to the variables 
        c = Constraint('C',var_array)
        array_new = list(itertools.product(*array))
        for k in range(0,len(array_new)):
            if sum(array_new[k]) == last_row[i]:
                array_sum.append(array_new[k])
            else:
                pass 
        c.add_satisfying_tuples(array_sum)
        tenner_csp.add_constraint(c)
     
    return tenner_csp,variable_array

