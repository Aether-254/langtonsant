import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0131 : checkSingleBlackFast (5, -1) 10294 .north (-3, 10) (-18, -19) = true := by
  decide +kernel

end LangtonsAnt
