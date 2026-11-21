import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0507 : checkSingleBlackFast (-7, 0) 19176 .north (-3, 6) (-3, -28) = true := by
  decide +kernel

end LangtonsAnt
