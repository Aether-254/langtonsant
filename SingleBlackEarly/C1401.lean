import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1401 : checkSingleBlackFast2 (-20, 6) 15633 .east (-2, -13) (-33, -19) = true := by
  decide +kernel

end LangtonsAnt
