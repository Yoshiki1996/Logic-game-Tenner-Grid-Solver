'''This project was mediated through Sheila McIlraith and is not 
to be copy and used for educational purposes which can lead to Academic Integrity'''

#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.  

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newVar=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newVar (newly instaniated variable) is an optional argument.
      if newVar is not None:
          then newVar is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newVar = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newVar = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
       
    #empty list to store all pruned values along with its variable 
    vals = []
    if newVar == None:
        #forward check all constraints 
        for c in csp.get_all_cons():
            #checking for one uninstantiated variable 
            if c.get_n_unasgn() == 1:
                #get all the variables the constraint is over 
                vars = c.get_unasgn_vars()
                for var in vars:
                    domain = var.cur_domain()
                    for i in range(0,len(domain)):
                        #If value satisfies constraint
                        if c.has_support(var,domain[i]) == True:
                            pass
                        #value does not satisfy constraint, therefore prune
                        elif c.has_support(var,domain[i]) == False:
                            if len(domain) == 0:
                                return False, vals 
                            else:
                                var.prune_value(domain[i])
                                vals.append((var,domain[i]))
                                print(vals)
                        else:
                            pass
    else:
        for c in csp.get_cons_with_var(newVar):
            #checking for one uninstantiated variable 
            if c.get_n_unasgn() == 1:
                #get all the variables the constraint is over 
                vars = c.get_unasgn_vars()
                for var in vars:
                    domain = var.cur_domain()
                    for i in range(0,len(domain)):
                        #If value satisfies constraint
                        if c.has_support(var,domain[i]) == True:
                            pass
                        #value does not satisfy constraint, therefore prune
                        elif c.has_support(var,domain[i]) == False:
                            if len(domain) == 0:
                                return False, vals
                            else:
                                var.prune_value(domain[i])
                                vals.append((var,domain[i]))
                        else:
                            pass
    return True, vals
       
#IMPLEMENT

def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    #initialize GAC_queue
    vals = []
    if newVar == None:
        #forward check all constraints
        GAC_queue = csp.get_all_cons()
        while GAC_queue:
            c = GAC_queue.pop(0)
            #if c.get_n_unasgn() == 1:
            #get all the variables the constraint is over 
            vars = c.get_unasgn_vars()
            for var in vars:
                domain = var.cur_domain()
                for i in range(0,len(domain)):
                    #If value satisfies constraint
                    if c.has_support(var,domain[i]) == True:
                        pass
                    #value does not satisfy constraint, therefore prune
                    elif c.has_support(var,domain[i]) == False:
                        if len(domain) == 0:
                            return False, vals 
                        else:
                            var.prune_value(domain[i])
                            vals.append((var,domain[i]))
                            #enqeue to GAC_queue for var in scope(C) and
                            #C not in GAC_queue
                            c_check = csp.get_cons_with_var(var)
                            for i in range(0,len(c_check)):
                                if c_check[i] not in GAC_queue:
                                    GAC_queue.insert(len(GAC_queue),c_check[i]) 
                                else:
                                    pass
                    else:
                        pass
    else:
        GAC_queue = csp.get_cons_with_var(newVar)
        while GAC_queue:
            c = GAC_queue.pop(0)
            #if c.get_n_unasgn() == 1:
            #get all the variables the constraint is over 
            vars = c.get_unasgn_vars()
            for var in vars:
                domain = var.cur_domain()
                for i in range(0,len(domain)):
                    #If value satisfies constraint
                    if c.has_support(var,domain[i]) == True:
                        pass
                    #value does not satisfy constraint, therefore prune
                    elif c.has_support(var,domain[i]) == False:
                        if len(domain) == 0:
                            return False, vals 
                        else:
                            var.prune_value(domain[i])
                            vals.append((var,domain[i]))
                            #enqeue to GAC_queue for var in scope(C) and
                            #C not in GAC_queue
                            c_check = csp.get_cons_with_var(var)
                            for i in range(0,len(c_check)):
                                if c_check[i] not in GAC_queue:
                                    GAC_queue.insert(len(GAC_queue),c_check[i]) 
                                else:
                                    pass
                    else:
                        pass  
        
    return True, vals

#IMPLEMENT







