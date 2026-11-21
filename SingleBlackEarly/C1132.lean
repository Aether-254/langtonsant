import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1132 : checkSingleBlackFast (27, -17) 10240 .north (-2, -1) (-26, 1) = true := by
  decide +kernel

end LangtonsAnt
