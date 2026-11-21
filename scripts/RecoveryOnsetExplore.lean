import ExactVariableRecovery

open LangtonsAnt

-- Discovery only; the proof module checks the selected boundary in the kernel.
#eval ((List.range 548).filter (fun j => recoveryColorBits (j + 104) != recoveryColorBits j)).getLast?
#eval (List.range 548).filter (fun j => 400 <= j && recoveryColorBits (j + 104) != recoveryColorBits j)
