import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1980 : checkSingleBlackFast2 (-72, -48) 15035 .west (23, 33) (-52, 13) = true := by
  decide +kernel

end LangtonsAnt
