import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0465 : checkSingleBlackFast (16, 13) 10696 .north (-6, 2) (2, -24) = true := by
  decide +kernel

end LangtonsAnt
