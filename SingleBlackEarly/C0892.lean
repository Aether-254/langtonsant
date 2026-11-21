import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0892 : checkSingleBlackFast (-7, -2) 9412 .north (-1, -2) (-23, 2) = true := by
  decide +kernel

end LangtonsAnt
