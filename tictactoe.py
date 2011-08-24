#! /usr/bin/env python
"""
Tic-tac-toe for an arbitrary sized board.

The Board class could be used to play the game interactively with a human 
or against the computer itself simulating either player in successive moves.

Some features-
1. Besides the board initialization, each call for best_slot() is stateless.
   In other words, as long as you update the state of the board using 
   add_placement() or set_board(), you could reuse the board object for 
   multiple (same sized) boards without worrying about any previous state.
2. You can also create a new board object for every move without caring about 
   previous state.   
3. Currently, these is no sanity check done for the board i.e. make sure 
   that the board has |num(X) - num(O)| <=1 or that X can not have more 
   pieced than O if it is X's turn. These were trivial to check but I 
   decided against it to allow random variations of the board. 
   It is a feature, not a bug :)

Features that could be added-
1. Select a slot at random when there are multiple slots with the same 
   (highest) weight.
2. Use some kind protocol buffer/thrift glue.
"""

import logging
import sys

logging.basicConfig(level=logging.WARNING)

def log_helper(name, c):
    logging.debug("%s (size = %d):\n%s\n" % (name, len(c), c))

# The markers X and O
pegs = 'OX'

def opposite(peg):
    return pegs.replace(peg, '')

def cross(s1, s2):
    return [e1+e2 for e1 in s1 for e2 in s2]

def diag(s1, s2):
    assert (len(s1) == len(s2))
    return [(s1[i]+s2[i]) for i in range(len(s1))]
    
class Board:
    """ 
    Representation of a nxn board of tic-tac-toe.
    
    Usage: 
        b = Board(3, 3, "..X|.O.|...")
        print b
        (best_slot, message) = b.best_slot('O')
        if best_slot != None:
            b.add_placement(best_slot, 'O')
            print b
            
            
    Innards:
        We ditched the game tree approach for this game and using enumeration
        of possible winning sets to find the next best slot for the game.
        Each move is independent and stateless - you may decide to use the same
        board object multiple times but it is not necessary to do so.
        
        How it works:
            (in _initialize_structures)
            Given the board constrains (board_size and win_size), we try to
            find all the set of slots that result in victory if all pegs in the 
            slot are of the same type. This is the win_sets structure.
            
            The slot_to_winsets structure maps each of the slot to the set of 
            win_sets that the slot influences. Essentially, these win_sets are 
            those which contain this slot.
            
            (in _best_offensive_move)
            Consider an offensive game (where P1 is only trying to finish his 
            m-in-a-row goal and not trying to stop his opponent).             
            P1 can win iff there is at least one win_set which has all pegs of his type.
            When iterating over the win_sets for P1, we first discard all win_sets
            that contain even a single peg of the opponent (using slot_to_winsets)
            - there is no way P1 can win by putting his peg in one of these.
            
            We get all the win_sets in can_win_sets. 
            For each of these win_sets, we look at every slot in the set and count
            the number of slots that already has P1's peg in it. A win_set that 
            has more number of P1's peg is lot more important for the player and 
            it is very important for P1 to be able to finish them. Hence, we give
            high weights to the empty slots in that win_set. This weight is 
            exponential based on the number of P1's pegs already present in the set.
            (The more finished a win_set is, the more important it is and so are all
            the vacant slots in the win_set).
            
            (in best_slot)
            We get a dict of weights for each available slots in the board.
            We now rerun the _best_offensive_move looking from the opponent's 
            point of view - as in which are the slots that are important for the 
            opponent to finish.
            
            These dicts (w1 and w2) are added together in a weighed proportion 
            (decided by defensiveness) to get the combined weights.
            By default, we use defensiveness = 5, which means the opponents' weight
            are 5 times more important fot us than our own. Which means that it is 
            a lot more important for us to stop the opponent from winning than to 
            win ourself.
            
            From the final dict, we pick a slot with the highest weight and return it
            as the best slot.
              
    """
    def __init__(self, board_size, win_size, board_string = None):
        assert(win_size <= board_size)
        self._board_size = board_size
        self._win_size = win_size
        self._initialize_structures()
        if board_string == None:
            board_string = ' ' * (self._board_size ** 2)
        self._placements = self._parse_board(board_string)

    def _initialize_structures(self):
        # This gives row index line as pretty alpha chars (a,b,c...)
        self._rows = map(lambda x:chr(97+x), range(self._board_size))
        self._cols = self._rows

        # All slots of the board (aa, ab, ac.. ba, bc..)
        self._slots = cross(self._rows, self._cols)
        assert(self._board_size ** 2 == len(self._slots))
        log_helper("self._slots", self._slots)

        # win_sets: All possible sets of contiguous slots, each of size m.
        # If at least one of these set has all pegs of the same kind,
        # that peg wins the game.
        # win_sets are computed in parts from 4 directional sets.
        n = self._board_size
        m = self._win_size
        k = n - m + 1
        vert_sets = [cross(r, self._cols[i:i+m]) \
                        for r in self._rows for i in range(k)] 
        horz_sets = [cross(self._rows[i:i+m], c) \
                        for c in self._cols for i in range(k)]
        dia1_sets = [diag(self._rows[i:i+m], self._cols[j:j+m]) \
                        for i in range(k) for j in range(k)]
        dia2_sets = [diag(self._rows[i:i+m], self._cols[j:j+m][::-1]) \
                        for i in range(k) for j in range(k)]

        self._win_sets = vert_sets + horz_sets + dia1_sets + dia2_sets
        assert(2*(2*n-m+1)*(n-m+1) == len(self._win_sets)) 
        log_helper("win_sets", self._win_sets);

        # The winning sets for each slot.
        # Map from every slot in the board to the set of wining_sets they influence.
        self._slot_to_winsets = dict((s, [m for m in self._win_sets if s in m]) \
                                     for s in self._slots)
        log_helper("slot_to_winsets", self._slot_to_winsets)

    def best_slot(self, my_peg, defensiveness = 5.0):
        """
        Returns tuple(best_slot, comment) 
        If best_slot is None, the game is over and reason is given in the comment.
        Find the best next slot for my_pegs for the board.
        defensiveness is the fuzz factor which decides whether it is more
        important to win ourself or stop the other player from winning.
        """
        empty_slots = [s for s in self._slots if self._placements[s] == ' '] 
        my_slots = [s for s in self._slots if self._placements[s] == my_peg] 
        opp_slots = [s for s in self._slots if self._placements[s] == opposite(my_peg)] 
        
        # If there are no more slots to play then report the game is over.
        if len(empty_slots) == 0:
            return (None, "GAME DRAW !!")
    
        (w1, i1) = self._best_offensive_move(my_peg, my_slots, opp_slots, empty_slots)        
        logging.info("== offensive slot weights for self ==\n" + self._board_string(w1)) 

        (w2, i2) = self._best_offensive_move(opposite(my_peg), opp_slots, my_slots, empty_slots)        
        logging.info("== offensive slot weights for opponent ==\n" + self._board_string(w2)) 

        if (i1 == 1):
            return (None, my_peg + " has won !!")
        if (i2 == 1):
            return (None, opposite(my_peg) + " has won !!")
        if (i1 == -1 and i2 == -1):
            return (None, "The game is draw !!")
    
        slot_weights = dict((s, w1[s] + defensiveness * w2[s]) for s in w1.keys())    
        logging.info("== aggregate slot weights for my next move ==\n" + self._board_string(slot_weights)) 
    
        best_slot = max(slot_weights, key=slot_weights.get)
        return (best_slot, '')

    def _best_offensive_move(self, p1_peg, p1_slots, p2_slots, empty_slots):    
        """
        Returns (slot_scores, indicator) tuple.
        slot_scores is a dict contains scores for each available slot.
        slot_scores are meaningful iff indicator == 0
        indicator == -1 means p1 can not win anymore.
        indicator ==  1 means p1 has won already.
        indicator ==  0 means continue playing.
        
        Given the current state of the board (described by sets of slots),
        returns the best move for p1 to finish one of his rows. 
        This does not (actively) try to disrupt the building plans of the 
        opponents (though this is used in reverse to do exactly that).
        """
        # Any slots that have the other players peg is no good for me.
        can_not_win_sets = sum([self._slot_to_winsets[s] for s in p2_slots], [])    
        log_helper("can_not_win_sets for %s" % p1_peg, can_not_win_sets)

        # Sets where p1 could still win.
        can_win_sets = [s for s in self._win_sets if s not in can_not_win_sets]   
        log_helper("can_win_sets for %s" % p1_peg, can_win_sets)

        win_indicator = 0
        # Can not win this game anymore
        if len(can_win_sets) == 0:
            win_indicator = -1
        
        slot_weights = dict((s, 0) for s in empty_slots)
        for cw in can_win_sets:
            # vacant_slots are slots that still need to be filled up for
            # each can_win set.
            vacant_slots = set(cw) - set(p1_slots)        
            # no vacant slot for a set == p1 won already 
            if len(vacant_slots) == 0:
                win_indicator = 1

            # s3cret sauce: the set is more important for p1 if it already
            # has more pegs filled in already (ie less vacancy).
            # and more important == exponentially more important.
            extra_weight = pow(5, self._win_size - len(vacant_slots))
            for s in vacant_slots:
                slot_weights[s] += extra_weight
        return (slot_weights, win_indicator)

    def add_placement(self, slot, peg):
        assert(self._placements.get(slot) == ' ')
        self._placements[slot] = peg
        
    def set_board(self, board_string):
        self._placements = self._parse_board(board_string)

    def _parse_board(self, board_str):
        """
        Read the board as a string.
        Valid characters are O and X and a space or dot for empty cell.
        Any other character is embellishment and is safely ignored.
        Returns a dict that maps each slot to the peg or ' ' if empty.
        """
        #TODO: Parse variations (ignore case, can use any char as delimiter)
        chars = [c for c in board_str.replace('.', ' ') if c in pegs + ' ']
        assert (self._board_size ** 2 == len(chars))
        return dict(zip(self._slots, chars))

    def _board_string(self, dict = None):
        if dict == None:
            dict = self._placements

        buffer = ''
        i = 0
        for s in self._slots:
            buffer += str(dict.get(s))
            i += 1
            if i % self._board_size != 0:
                buffer += ' | '
            elif i < self._board_size ** 2: 
                buffer += '\n' + "----" * self._board_size + '\n'
        return buffer

    def __str__(self):
        return self._board_string()

def main(argv):
    n = 5
    m = 4
    if len(argv) > 1:
        n = int(sys.argv[1])
    if len(argv) > 2:
        m = int(sys.argv[2])

    b = Board(n, m)
    print b
    player = "O"
    while True:
         (next_slot, status) = b.best_slot(player)
         if next_slot != None:
             print "%s should play at %s.\n" % (player, next_slot)
             b.add_placement(next_slot, player)
             print b         
             player = opposite(player)
             raw_input('Press Enter.............')
         else:
             print status
             break
             
if __name__ == '__main__':
    main(sys.argv)