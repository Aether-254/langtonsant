import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0988 : checkSingleBlackFast (-2, 19) 20072 .north (-6, 3) (-6, -31) = true := by
  decide +kernel

end LangtonsAnt
