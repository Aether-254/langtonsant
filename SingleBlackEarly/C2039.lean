import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2039 : checkSingleBlackFast (-78, -52) 13564 .north (28, 20) (-54, -36) = true := by
  decide +kernel

end LangtonsAnt
