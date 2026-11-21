import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1119 : checkSingleBlackFast (25, -12) 10264 .north (-2, -2) (-26, 0) = true := by
  decide +kernel

end LangtonsAnt
