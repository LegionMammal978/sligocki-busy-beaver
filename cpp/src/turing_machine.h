#ifndef BUSY_BEAVER_TURING_MACHINE_H_
#define BUSY_BEAVER_TURING_MACHINE_H_

#include <set>
#include <string>
#include <vector>


namespace busy_beaver {

using Symbol = int;
using State = int;
const Symbol BlankSymbol = 0;
const State InitialState = 0;
const State HaltState = -1;

enum Dir {
  LEFT = -1,
  RIGHT = +1
};

class TuringMachine {
 public:
  struct LookupResult {
    Symbol symbol;
    Dir move;
    State state;
    bool undecided = false;
  };

  LookupResult Lookup(State state, Symbol symbol) const {
    return transitions_[state][symbol];
  }


  int num_states() const { return num_states_; }
  int num_symbols() const { return num_symbols_; }
  State max_next_state() const { return max_next_state_; }
  Symbol max_next_symbol() const { return max_next_symbol_; }
  bool next_move_left_ok() const { return next_move_left_ok_; }
  int num_halts() const { return num_halts_; }
  const std::string& hereditary_name() const { return hereditary_name_; }

  // Empty TM
  TuringMachine(int num_states, int num_symbols);

  // TM from transition table.
  // Note: This inefficiently copies the table. Currently it's only used for
  // small loads, so it's not critical. But if it's used more places, we should
  // update this to use unique_ptr or something like that.
  TuringMachine(const std::vector<std::vector<LookupResult>>& transitions,
                const std::string& base_name);

  // TM built from a previous TM
  TuringMachine(const TuringMachine& old_tm,
                const State& last_state, const Symbol& last_symbol,
                const LookupResult& next_trans,
                int hereditary_sub_order);

 private:
  int num_states_;
  int num_symbols_;
  State max_next_state_;
  Symbol max_next_symbol_;
  bool next_move_left_ok_;
  int num_halts_;
  std::string hereditary_name_;
  std::vector<std::vector<LookupResult>> transitions_;
};

// Standard halt transition: 1RZ
const TuringMachine::LookupResult HALT_TRANS = {1 /* symbol */, RIGHT, HaltState};

// Write TM to outstream in a human-readable format.
void WriteTuringMachine(const TuringMachine& tm, std::ostream* outstream);

// Read one TM from text or file (written in WriteTuringMachine() format).
// Returns nullptr if there are no TMs left.
TuringMachine* ReadTuringMachineStr(const std::string& tm_str,
                                    const std::string& base_name = "");
TuringMachine* ReadTuringMachineStream(std::istream* instream,
                                       const std::string& base_name = "");
TuringMachine* ReadTuringMachineFile(const std::string& filename,
                                     const long line_num);

}  // namespace busy_beaver

#endif  // BUSY_BEAVER_TURING_MACHINE_H_
