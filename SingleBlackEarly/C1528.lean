import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1528 : checkSingleBlackFast (-28, -8) 28900 .north (1, 5) (-9, -39) = true := by
  decide +kernel

end LangtonsAnt
