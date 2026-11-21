import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1358 : checkSingleBlackFast (-16, 5) 19420 .north (-6, -1) (0, -29) = true := by
  decide +kernel

end LangtonsAnt
