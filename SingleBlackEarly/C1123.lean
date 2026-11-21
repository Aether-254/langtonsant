import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1123 : checkSingleBlackFast (23, -18) 10356 .north (0, 1) (-24, 3) = true := by
  decide +kernel

end LangtonsAnt
