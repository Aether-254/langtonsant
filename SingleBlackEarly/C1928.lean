import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1928 : checkSingleBlackFast2 (-68, -40) 17513 .west (27, 33) (-53, 10) = true := by
  decide +kernel

end LangtonsAnt
