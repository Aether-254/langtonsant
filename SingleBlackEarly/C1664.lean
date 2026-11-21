import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1664 : checkSingleBlackFast2 (-44, -16) 16265 .west (15, 21) (-41, -2) = true := by
  decide +kernel

end LangtonsAnt
