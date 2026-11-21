import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1818 : checkSingleBlackFast2 (-58, -30) 16993 .west (22, 28) (-48, 5) = true := by
  decide +kernel

end LangtonsAnt
