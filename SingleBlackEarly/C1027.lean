import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1027 : checkSingleBlackFast (-7, 17) 8936 .north (-1, -4) (-23, 0) = true := by
  decide +kernel

end LangtonsAnt
