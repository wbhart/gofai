class TList:
    """Structure to contain parsed text strings for a window. Each line
       contains a parsed statement.
    """
    def __init__(self):
        self.data = [] # list of ASTs in window
        self.line = 0 # which line of text does cursor line correspond to
        self.dep = dict() # dependency on target

    def __setitem__(self, key, value):
        """Overload array notation so lines can be added.
        """
        if key == len(self.data): # normal array notation doesn't allow append
            self.data.append(value)
        else:
            self.data[key] = value

    def len(self):
        """Return number of lines in structure.
        """
        return len(self.data)

    def dependency(self, i):
        if i in self.dep:
            return self.dep[i]
        return -1 

class TreeList:
    """Structure containing TreeLists for each of the windows 0-2 and which one
       has focus.
    """
    def __init__(self):
        self.tlist0 = TList()
        self.tlist1 = TList()
        self.tlist2 = TList()
        self.focus = self.tlist0
        self.vars = dict() # variables used
        self.tars = dict() # targets used

    def switch_list(self):
        if self.focus == self.tlist0:
            self.focus = self.tlist1
        elif self.focus == self.tlist1:
            self.focus = self.tlist2
        else:
            self.focus = self.tlist0

